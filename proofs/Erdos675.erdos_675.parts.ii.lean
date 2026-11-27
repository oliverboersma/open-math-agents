import FormalConjectures.ErdosProblems.«675»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.ZMod.Basic

/-!
The construction forces into one part the new prime factors of finitely
many translated integers at each stage. The multiplier is chosen so these
factors lie beyond a long interval above the stage cutoff. Chebyshev's
bounds keep the forced primes a small fraction of all primes.

The next stage starts beyond all primes forced in the current stage. The
final partition places all forced primes and all even-indexed primes in
one part. The remaining odd-indexed primes give the other part a positive
proportion. The primorial multiplier preserves divisibility by every
prime below the cutoff, so each stage gives the required translation.

Credit: @Genbox.
-/

open Finset Filter Real Asymptotics
open scoped Topology Chebyshev Nat.Prime

namespace OMA

private theorem prime_count_bounds :
    ∀ᶠ x : ℕ in atTop, (x:ℝ)/(2*log x) ≤ (π x:ℝ) ∧ (π x:ℝ) ≤ 5*(x:ℝ)/log x := by
  have h₂ := log_lt_sub_one_of_pos (by norm_num : 0 < (2:ℝ)⁻¹) (by norm_num)
  rw [log_inv] at h₂
  norm_num at h₂
  let δ := log 2 - 1/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hl : ∀ᶠ x : ℕ in atTop, log ((x:ℝ)+1) ≤ δ*(x:ℝ) := by
    have hlimit : Tendsto (fun x : ℕ => (x:ℝ)+1) atTop atTop :=
      tendsto_atTop.2 fun M =>
        (tendsto_atTop.1 tendsto_natCast_atTop_atTop M).mono fun _ h => by linarith
    have hsmall := hlimit.eventually (isLittleO_log_id_atTop.bound (c := δ/3) (by positivity))
    filter_upwards [hsmall, eventually_ge_atTop (1:ℕ)] with x hx hx1
    have hx' : (1:ℝ) ≤ x := by exact_mod_cast hx1
    have hlog : 0 ≤ log ((x:ℝ)+1) := log_nonneg (by linarith)
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hlog,
      abs_of_nonneg (show 0 ≤ (x:ℝ)+1 by positivity)] at hx
    have he : (x:ℝ)+1 ≤ 3*(x:ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left he (show 0≤δ/3 by positivity)]
  have hroot : ∀ᶠ x : ℕ in atTop, log (x:ℝ) ≤ √(x:ℝ) := by
    have ht := (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).bound (c := 1) (by norm_num)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually ht, eventually_ge_atTop (1:ℕ)]
      with x hx hx1
    have h1 : (1:ℝ) ≤ x := by exact_mod_cast hx1
    have hp : 0 ≤ (x:ℝ)^(1/2:ℝ) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg (log_nonneg h1), abs_of_nonneg hp, one_mul] at hx
    rw [sqrt_eq_rpow]
    exact hx
  filter_upwards [hl,hroot,eventually_ge_atTop (2:ℕ)] with x hx hroot hx₂
  have hx1 : (1:ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < log (x:ℝ) := log_pos hx1
  have hlo := Chebyshev.pi_ge x
  constructor
  · apply le_trans _ hlo
    rw [show (x:ℝ)/(2*log x) = ((x:ℝ)/2)/log x by field_simp]
    apply div_le_div_of_nonneg_right _ hlog.le
    dsimp [δ] at hx
    linarith
  · have hh := Chebyshev.pi_le_log4_mul_div hx1
    rw [Nat.floor_natCast, log_sqrt (le_of_lt (by linarith : (0:ℝ)<x))] at hh
    apply hh.trans
    have log4 : log (4:ℝ) ≤ 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have hz : √(x:ℝ)*log (x:ℝ) ≤ x := by
      have he := mul_le_mul_of_nonneg_left hroot (sqrt_nonneg (x:ℝ))
      nlinarith [sq_sqrt (Nat.cast_nonneg (α := ℝ) x)]
    apply (le_div_iff₀ hlog).2
    have heq : (log (4:ℝ)*(x:ℝ)/(log (x:ℝ)/2))*log (x:ℝ) =
        2*log 4*(x:ℝ) := by field_simp
    rw [add_mul,heq]
    nlinarith [mul_le_mul_of_nonneg_right log4 (Nat.cast_nonneg (α := ℝ) x)]

private def primorial (Y : ℕ) := ∏ p ∈ Nat.primesLE Y, p

private theorem primorial_pos (Y : ℕ) : 0 < primorial Y :=
  prod_pos (fun _ hp => (Nat.prime_of_mem_primesLE hp).pos)

private theorem prime_dvd_primorial {p Y : ℕ} (hp : p.Prime) :
    p ∣ primorial Y ↔ p ≤ Y := by
  unfold primorial
  constructor
  · intro hd
    obtain ⟨q,hq,hpq⟩ := (hp.prime.dvd_finsetProd_iff (S := Nat.primesLE Y) id).mp hd
    have he := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primesLE hq)).mp hpq
    rw [he]
    exact Nat.le_of_mem_primesLE hq
  · intro h
    exact dvd_prod_of_mem id (Nat.mem_primesLE.mpr ⟨h,hp⟩)

private theorem log_primorial (Y : ℕ) : log (primorial Y:ℝ) ≤ 2*(Y:ℝ) := by
  have he : log (primorial Y:ℝ) = θ (Y:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, primorial, Nat.cast_prod, log_prod]
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero
  rw [he]
  apply (Chebyshev.theta_le_log4_mul_x (by positivity)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [show (4:ℝ)=2^2 by norm_num,log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

private theorem count_bad_multipliers {Y k p a : ℕ} (hp : p.Prime) (hpY : Y < p) :
    ((Icc 1 (k*Y)).filter (fun m => p ∣ a+primorial Y*m)).card ≤ k+1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have hM : (primorial Y:ZMod p) ≠ 0 :=
    fun h => hpY.not_ge ((prime_dvd_primorial hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp h))
  have hcard := card_le_card_of_injOn (fun m : ℕ => m/p) (t := range (k+1)) (s :=
    (Icc 1 (k*Y)).filter (fun m => p ∣ a+primorial Y*m)) (by
    intro m hm
    have h₁ := (mem_Icc.mp (mem_filter.mp hm).1).2
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hp.pos).2
      (h₁.trans_lt (lt_of_le_of_lt (Nat.mul_le_mul_left k hpY.le) (by
        rw [Nat.add_mul,one_mul]; exact Nat.lt_add_of_pos_right hp.pos))))) (by
    intro m hm n hn he
    have hm' := (ZMod.natCast_eq_zero_iff _ p).2 (mem_filter.mp hm).2
    have hn' := (ZMod.natCast_eq_zero_iff _ p).2 (mem_filter.mp hn).2
    push_cast at hm' hn'
    have hc : (m:ZMod p) = (n:ZMod p) :=
      mul_left_cancel₀ hM (add_left_cancel (hm'.trans hn'.symm))
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hc
    change m/p = n/p at he
    calc
      m = m%p+p*(m/p) := (Nat.mod_add_div m p).symm
      _ = n%p+p*(n/p) := by rw [hmod,he]
      _ = n := Nat.mod_add_div n p)
  simpa using hcard

private theorem avoids_middle {s Y k : ℕ} (hs : s*(k+1)*π (k*Y) < k*Y) :
    ∃ m ∈ Icc 1 (k*Y), ∀ a ∈ Icc 1 s, ∀ p ∈ Nat.primesLE (k*Y),
      Y < p → ¬p ∣ a+primorial Y*m := by
  classical
  let P := (Nat.primesLE (k*Y)).filter (fun p => Y < p)
  let A := Icc 1 s
  let U := Icc 1 (k*Y)
  let bad (z : ℕ × ℕ) := U.filter (fun m => z.2 ∣ z.1+primorial Y*m)
  let S := (A ×ˢ P).biUnion bad
  have hsum : S.card ≤ ∑ z ∈ A ×ˢ P, (bad z).card := card_biUnion_le
  have hcount : (A ×ˢ P).card ≤ s*π (k*Y) := by
    have hP := card_filter_le (Nat.primesLE (k*Y)) (fun p => Y < p)
    rw [Nat.primesLE_card_eq_primeCounting] at hP
    have hA : A.card = s := by simp [A,Nat.card_Icc]
    rw [card_product,hA]
    exact Nat.mul_le_mul_left s hP
  have hcard : S.card < U.card := by
    have hh : (∑ z ∈ A ×ˢ P, (bad z).card) ≤ (A ×ˢ P).card*(k+1) := by
      calc
        _ ≤ ∑ _ ∈ A ×ˢ P, (k+1) := by
          apply sum_le_sum
          intro z hz
          have hq := mem_filter.mp (mem_product.mp hz).2
          exact count_bad_multipliers (Nat.prime_of_mem_primesLE hq.1) hq.2
        _ = _ := by simp
    have he : S.card ≤ s*(k+1)*π (k*Y) :=
      (hsum.trans (hh.trans (Nat.mul_le_mul_right _ hcount))).trans (by rw [mul_right_comm])
    simpa [U,Nat.card_Icc] using he.trans_lt hs
  obtain ⟨m,hm,hS⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨m,hm,fun a ha p hp hpY hd => hS ?_⟩
  exact mem_biUnion.mpr ⟨(a,p), mem_product.mpr ⟨ha,mem_filter.mpr ⟨hp,hpY⟩⟩,
    mem_filter.mpr ⟨hm,hd⟩⟩

end OMA

namespace OMA

private def fresh (s Y t : ℕ) : Finset ℕ :=
  ((Icc 1 s).biUnion (fun a => (a+t).primeFactors)).filter (fun p => Y < p)

private theorem mem_fresh {s Y t p : ℕ} :
    p ∈ fresh s Y t ↔ Y < p ∧ p.Prime ∧ ∃ a ∈ Icc 1 s, p ∣ a+t := by
  simp only [fresh,mem_filter,mem_biUnion,Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨a,ha,hp,hd,_⟩,hY⟩
    exact ⟨hY,hp,a,ha,hd⟩
  · rintro ⟨hY,hp,a,ha,hd⟩
    exact ⟨⟨a,ha,hp,hd,by have := (mem_Icc.mp ha).1; omega⟩,hY⟩

private theorem fresh_log_bound {s Y t Z : ℕ}
    (hZ : 1 ≤ Z) (hf : ∀ p ∈ fresh s Y t, Z < p) :
    ((fresh s Y t).card:ℝ)*log (Z:ℝ) ≤ (s:ℝ)*log ((s+t:ℕ):ℝ) := by
  let S := fresh s Y t
  let N := ∏ a ∈ Icc 1 s, (a+t)
  have hpos : 0 < N := by
    unfold N
    apply prod_pos
    intro a ha
    have := (mem_Icc.mp ha).1
    omega
  have hsub : S ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨_,hp,a,ha,hd⟩ := mem_fresh.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hp,hd.trans (dvd_prod_of_mem (fun a : ℕ => a+t) ha),hpos.ne'⟩
  have hdiv : ∏ p ∈ S, p ∣ N :=
    (prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd N)
  have hprod : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => (mem_fresh.mp hp).2.1.pos)
  have hlog :
      ∑ p ∈ S, log (p:ℝ) ≤ ∑ a ∈ Icc 1 s, log ((a+t:ℕ):ℝ) := by
    have hle : (↑(∏ p ∈ S,p):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.le_of_dvd hpos hdiv
    have h := log_le_log (by positivity : 0 < (↑(∏ p ∈ S,p):ℝ)) hle
    rw [Nat.cast_prod,log_prod (fun p hp => by exact_mod_cast (mem_fresh.mp hp).2.1.ne_zero)] at h
    rw [show (N:ℝ) = ∏ a ∈ Icc 1 s, ((a+t:ℕ):ℝ) by simp [N], log_prod] at h
    · exact h
    · intro a ha
      exact_mod_cast (show a+t ≠ 0 by have := (mem_Icc.mp ha).1; omega)
  have hlower :
      (∑ _ ∈ S, log (Z:ℝ)) ≤ ∑ p ∈ S, log (p:ℝ) := by
    apply sum_le_sum
    intro p hp
    exact log_le_log (by positivity) (by exact_mod_cast (hf p hp).le)
  have hupper :
      (∑ a ∈ Icc 1 s, log ((a+t:ℕ):ℝ)) ≤ ∑ _ ∈ Icc 1 s, log ((s+t:ℕ):ℝ) := by
    apply sum_le_sum
    intro a ha
    have ha' := (mem_Icc.mp ha).1
    exact log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (mem_Icc.mp ha).2 t)
  have hh := hlower.trans (hlog.trans hupper)
  simpa [S,Nat.card_Icc,nsmul_eq_mul] using hh

private structure Block (s : ℕ) where
  base : ℕ
  far : ℕ
  cap : ℕ
  period : ℕ
  forced : Finset ℕ
  pattern_le : s ≤ base
  base_le_cap : base ≤ cap
  period_pos : 0 < period
  small_factor : ∀ p : ℕ, p.Prime → p ≤ base → p ∣ period
  fresh_factor : ∀ a ∈ Icc 1 s, ∀ p : ℕ, p.Prime → base < p → p ∣ a+period → p ∈ forced
  forced_spec : ∀ p ∈ forced, p.Prime ∧ far < p ∧ base < p ∧ p ≤ cap
  budget : 8*forced.card ≤ π far

private theorem mul_atTop_nat {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun Y : ℕ => k*Y) atTop atTop :=
  tendsto_atTop_atTop.2 fun n =>
    ⟨n,fun _ hY => hY.trans (le_mul_of_one_le_left (Nat.zero_le _) hk)⟩

private theorem block_exists {s : ℕ} (hs : 1 ≤ s) (old : ℕ) :
    ∃ b : Block s, old < b.base ∧ 8*old ≤ π b.base := by
  let k := 100*s
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hprime := (mul_atTop_nat hk).eventually prime_count_bounds
  have hbase := tendsto_atTop.1 Nat.tendsto_primeCounting (8*old)
  have hlog : Tendsto (fun Y : ℕ => log (Y:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLg := tendsto_atTop.1 hlog (5*(s:ℝ)*(k+1)+1)
  have hsmall :
      ∀ᶠ Y : ℕ in atTop, log ((s+k:ℕ):ℝ) + log (Y:ℝ) ≤ (Y:ℝ) := by
    have hB := isLittleO_log_id_atTop.bound (c := 1/2) (by norm_num)
    have hC := tendsto_atTop.1 tendsto_natCast_atTop_atTop (2*log ((s+k:ℕ):ℝ))
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hB,hC,eventually_ge_atTop (1:ℕ)] with Y hB hC hY
    have hY' : (1:ℝ) ≤ Y := by exact_mod_cast hY
    simp only [id, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hY'),
      abs_of_nonneg (show (0:ℝ) ≤ Y by positivity)] at hB
    linarith
  obtain ⟨Y,hYp,hYπ,hYL,hYs,hYb⟩ := (hprime.and (hbase.and (hLg.and
    (hsmall.and (eventually_ge_atTop (max s (max (old+1) 2))))))).exists
  let Z := k*Y
  have hY : 2 ≤ Y := by omega
  have hY' : (1:ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hYZ : Y ≤ Z := le_mul_of_one_le_left (Nat.zero_le _) hk
  have hZ : (0:ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hLgZ : 0 < log (Z:ℝ) := log_pos (hY'.trans_le (by exact_mod_cast hYZ))
  have hLgYL : log (Y:ℝ) ≤ log (Z:ℝ) :=
    log_le_log (by positivity) (by exact_mod_cast hYZ)
  have hS : s*(k+1)*π Z < Z := by
    have h := hYp.2
    change (π Z:ℝ) ≤ 5*(Z:ℝ)/log (Z:ℝ) at h
    have hh := (le_div_iff₀ hLgZ).1 h
    have hcoeff : 5*(s:ℝ)*((k:ℝ)+1) < log (Z:ℝ) := by linarith
    have hg := mul_lt_mul_of_pos_right hcoeff hZ
    have hsc := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ (s:ℝ)*((k:ℝ)+1) by positivity)
    have ht : (s:ℝ)*((k:ℝ)+1)*(π Z:ℝ) < (Z:ℝ) := by
      apply (lt_of_mul_lt_mul_right _ hLgZ.le)
      nlinarith
    exact_mod_cast ht
  obtain ⟨m,hm,hmavo⟩ := avoids_middle hS
  let t := primorial Y*m
  let cap := s+primorial Y*Z
  have ht : 0 < t := Nat.mul_pos (primorial_pos _) (mem_Icc.mp hm).1
  have htZ : t ≤ primorial Y*Z := Nat.mul_le_mul_left _ (mem_Icc.mp hm).2
  let F := fresh s Y t
  have hF (p : ℕ) (hp : p ∈ F) : p.Prime ∧ Z<p ∧ Y<p ∧ p≤cap := by
    obtain ⟨hY',hp,a,ha,hd⟩ := mem_fresh.mp hp
    have hAZ := (mem_Icc.mp ha).2
    have hPt : p ≤ a+t := Nat.le_of_dvd (by omega) hd
    refine ⟨hp,?_ ,hY', hPt.trans (Nat.add_le_add hAZ htZ)⟩
    by_contra! hle
    exact hmavo a ha p (Nat.mem_primesLE.mpr ⟨hle,hp⟩) hY' hd
  have hlog : log ((s+t:ℕ):ℝ) ≤ 3*(Y:ℝ) := by
    have hpr : 0 < (primorial Y:ℝ) := by exact_mod_cast primorial_pos Y
    have h₁ : s+t ≤ primorial Y*(s+Z) := by
      have h₀ : s ≤ primorial Y*s := le_mul_of_one_le_left (Nat.zero_le _) (primorial_pos Y)
      nlinarith
    have h₂ : s+Z ≤ (s+k)*Y := by
      have h₀ : s ≤ s*Y := le_mul_of_one_le_right (Nat.zero_le _) (by omega)
      dsimp [Z]
      nlinarith
    have h₃ : log ((s+Z:ℕ):ℝ) ≤ (Y:ℝ) := by
      have hh := log_le_log (by positivity : 0 < ((s+Z:ℕ):ℝ)) (show ((s+Z:ℕ):ℝ) ≤ (((s+k)*Y:ℕ):ℝ) by exact_mod_cast h₂)
      rw [Nat.cast_mul,log_mul (by positivity) (by positivity)] at hh
      exact hh.trans hYs
    have hh := log_le_log (by positivity : 0 < ((s+t:ℕ):ℝ)) (show ((s+t:ℕ):ℝ) ≤ ((primorial Y*(s+Z):ℕ):ℝ) by exact_mod_cast h₁)
    rw [Nat.cast_mul,log_mul (by positivity) (by positivity)] at hh
    linarith [log_primorial Y]
  have hB : 8*F.card ≤ π Z := by
    have h := fresh_log_bound (s := s) (Y := Y) (t := t) (Z := Z) (by omega)
      (fun p hp => (hF p hp).2.1)
    have h₁ : (F.card:ℝ)*log (Z:ℝ) ≤ 3*(s:ℝ)*(Y:ℝ) := by
      have e := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (s:ℝ) by positivity)
      linarith
    have hp := hYp.1
    change (Z:ℝ)/(2*log (Z:ℝ)) ≤ (π Z:ℝ) at hp
    have h₂ := (div_le_iff₀ (by positivity : 0<2*log (Z:ℝ))).1 hp
    have hZeq : (Z:ℝ) = 100*(s:ℝ)*(Y:ℝ) := by simp [Z,k,Nat.cast_mul,mul_assoc]
    have h₃ : 8*(F.card:ℝ) ≤ (π Z:ℝ) := by
      apply le_of_mul_le_mul_right _ hLgZ
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) s) (Nat.cast_nonneg (α := ℝ) Y)]
    exact_mod_cast h₃
  have hYcap : Y ≤ cap :=
    hYZ.trans ((le_mul_of_one_le_left (Nat.zero_le _) (primorial_pos Y)).trans (Nat.le_add_left _ _))
  let b : Block s := {
    base := Y
    far := Z
    cap := cap
    period := t
    forced := F
    pattern_le := le_max_left _ _ |>.trans hYb
    base_le_cap := hYcap
    period_pos := ht
    small_factor := fun p hp hpY => dvd_mul_of_dvd_left ((prime_dvd_primorial hp).2 hpY) m
    fresh_factor := fun a ha p hp hpY hd => mem_fresh.mpr ⟨hpY,hp,a,ha,hd⟩
    forced_spec := hF
    budget := hB
  }
  refine ⟨b,?_,hYπ⟩
  change old < Y
  have he := (le_max_left (old+1) 2).trans ((le_max_right s _).trans hYb)
  omega

end OMA

namespace OMA

private noncomputable def chooseBlock (n old : ℕ) : Block (n+1) :=
  Classical.choose (block_exists (show 1 ≤ n+1 by omega) old)

private theorem chooseBlock_properties (n old : ℕ) :
    old < (chooseBlock n old).base ∧ 8*old ≤ π (chooseBlock n old).base :=
  Classical.choose_spec (block_exists (show 1 ≤ n+1 by omega) old)

private noncomputable def blocks : (n : ℕ) → Block (n+1)
  | 0 => chooseBlock 0 0
  | n+1 => chooseBlock (n+1) (blocks n).cap

private theorem next_base (n : ℕ) :
    (blocks n).cap < (blocks (n+1)).base ∧ 8*(blocks n).cap ≤ π (blocks (n+1)).base :=
  chooseBlock_properties (n+1) (blocks n).cap

private theorem mono_base : StrictMono (fun n => (blocks n).base) :=
  strictMono_nat_of_lt_succ (fun n => (blocks n).base_le_cap.trans_lt (next_base n).1)

private theorem mono_cap : StrictMono (fun n => (blocks n).cap) :=
  strictMono_nat_of_lt_succ (fun n => (next_base n).1.trans_le (blocks (n+1)).base_le_cap)

private theorem get_block {x : ℕ} (hx : (blocks 0).base ≤ x) :
    ∃ n : ℕ, (blocks n).base ≤ x ∧ x < (blocks (n+1)).base := by
  classical
  have he : ∃ i : ℕ, x < (blocks (i+1)).base :=
    ⟨x,(by omega : x < x+1+1).trans_le (blocks (x+1)).pattern_le⟩
  let n := Nat.find he
  refine ⟨n,?_,Nat.find_spec he⟩
  cases hn : n with
  | zero => exact hx
  | succ j =>
    have hj : j < Nat.find he := by change j<n; omega
    exact le_of_not_gt (Nat.find_min he hj)

private def forcedPrimes : Set ℕ := {p | ∃ i, p ∈ (blocks i).forced}

private theorem forced_prime {p : ℕ} (hp : p ∈ forcedPrimes) : p.Prime := by
  obtain ⟨i,hi⟩ := hp
  exact ((blocks i).forced_spec p hi).1

private theorem later_budget (n x : ℕ) :
    8*((blocks n).forced.filter (fun p => p ≤ x)).card ≤ π x := by
  by_cases hfar : (blocks n).far < x
  · have hc := card_filter_le (blocks n).forced (fun p => p ≤ x)
    exact (Nat.mul_le_mul_left _ hc).trans ((blocks n).budget.trans
      (Nat.monotone_primeCounting hfar.le))
  · have he : (blocks n).forced.filter (fun p => p ≤ x) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun p hp => ?_
      obtain ⟨hmem,hpx⟩ := mem_filter.mp hp
      exact hfar (((blocks n).forced_spec p hmem).2.1.trans_le hpx)
    simp [he]

open scoped Classical in
private theorem forced_sparse :
    ∀ᶠ x : ℕ in atTop, 4*((Nat.primesLE x).filter (fun p => p ∈ forcedPrimes)).card ≤ π x := by
  classical
  filter_upwards [eventually_ge_atTop (blocks 0).base] with x hx
  obtain ⟨n,hn,hn'⟩ := get_block hx
  let old := match n with
    | 0 => 0
    | j+1 => (blocks j).cap
  let S := (Nat.primesLE x).filter (fun p => p ∈ forcedPrimes)
  let T := Icc 1 old
  let U := (blocks n).forced.filter (fun p => p ≤ x)
  have hOld : 8*old ≤ π x := by
    cases n with
    | zero => simp [old]
    | succ j =>
      exact (next_base j).2.trans (Nat.monotone_primeCounting hn)
  have hS : S ⊆ T ∪ U := by
    intro p hp
    obtain ⟨hpxp,hpf⟩ := mem_filter.mp hp
    have hpx := Nat.le_of_mem_primesLE hpxp
    obtain ⟨i,hi⟩ := hpf
    have hPi := ((blocks i).forced_spec p hi)
    have hi' : i ≤ n := by
      by_contra! he
      have hle := mono_base.monotone (show n+1 ≤ i by omega)
      omega
    obtain rfl | hlt := hi'.eq_or_lt
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,hpx⟩)
    · apply mem_union_left
      cases n with
      | zero => omega
      | succ j =>
        have hle := (mono_cap.monotone (show i ≤ j by omega))
        exact mem_Icc.mpr ⟨hPi.1.one_le,hPi.2.2.2.trans hle⟩
  have hC := (card_le_card hS).trans (card_union_le T U)
  have hT : T.card = old := by simp [T,Nat.card_Icc]
  rw [hT] at hC
  have hu : 8*U.card ≤ π x := later_budget n x
  show 4*S.card ≤ π x
  omega

private def leftPrimes : Set ℕ :=
  forcedPrimes ∪ {p | p.Prime ∧ π' p % 2 = 0}

private theorem left_prime : leftPrimes ⊆ {p : ℕ | p.Prime} := by
  intro p hp
  exact hp.elim forced_prime And.left

private theorem parity_bound (x e : ℕ) (he : e ≤ 1) :
    (π x)/2 ≤ ((Nat.primesLE x).filter (fun p => π' p %2 = e)).card := by
  classical
  let f (j : ℕ) := Nat.nth Nat.Prime (2*j+e)
  have hf := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective
  have hCard := card_le_card_of_injOn f (s := range ((π x)/2))
    (t := (Nat.primesLE x).filter (fun p => π' p %2 = e)) (by
      intro j hj
      have hJ := mem_range.mp hj
      have hel : 2*j+e < π x := by omega
      have hp : f j ≤ x := by
        exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count (p := Nat.Prime) hel)
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hp,Nat.prime_nth_prime _⟩,by
        simp only [f,Nat.primeCounting'_nth_eq]; omega⟩) (by
      intro i hi j hj hh
      have he := hf hh
      omega)
  simpa using hCard

private theorem both_counts :
    ∀ᶠ x : ℕ in atTop,
      π x ≤ 8*((leftPrimes ∩ Set.Iic x).ncard) ∧
      π x ≤ 8*((({p : ℕ | p.Prime} \ leftPrimes) ∩ Set.Iic x).ncard) := by
  classical
  have hπ := tendsto_atTop.1 Nat.tendsto_primeCounting 8
  filter_upwards [forced_sparse,hπ] with x hf hx
  let B := Nat.primesLE x
  let F := B.filter (fun p => p ∈ forcedPrimes)
  let L := B.filter (fun p => p ∈ leftPrimes)
  let R := B.filter (fun p => p ∉ leftPrimes)
  let E := B.filter (fun p => π' p %2 = 0)
  let O := B.filter (fun p => π' p %2 = 1)
  have hE : E ⊆ L := by
    intro p hp
    obtain ⟨hp',hE'⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp',Or.inr ⟨Nat.prime_of_mem_primesLE hp',hE'⟩⟩
  have hO : O ⊆ R ∪ F := by
    intro p hp
    obtain ⟨hp',hO'⟩ := mem_filter.mp hp
    by_cases hFp : p ∈ forcedPrimes
    · exact mem_union_right _ (mem_filter.mpr ⟨hp',hFp⟩)
    · apply mem_union_left
      refine mem_filter.mpr ⟨hp',fun hh => hh.elim hFp ?_⟩
      rintro ⟨_,he⟩
      omega
  have hL := (parity_bound x 0 (by decide)).trans (card_le_card hE)
  have hR := (parity_bound x 1 (by decide)).trans
    ((card_le_card hO).trans (card_union_le R F))
  have hLC : (L : Set ℕ) = leftPrimes ∩ Set.Iic x := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp',hleft⟩ := mem_filter.mp hp
      exact ⟨hleft,Nat.le_of_mem_primesLE hp'⟩
    · intro hp
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hp.2,left_prime hp.1⟩,hp.1⟩
  have hRC : (R : Set ℕ) = ({p : ℕ | p.Prime} \ leftPrimes) ∩ Set.Iic x := by
    ext p
    simp [R,B,Nat.mem_primesLE, and_left_comm, and_comm]
  rw [← hLC,← hRC,Set.ncard_coe_finset,Set.ncard_coe_finset]
  change 4*F.card ≤ π x at hf
  change (π x)/2 ≤ L.card at hL
  change (π x)/2 ≤ R.card+F.card at hR
  omega

private theorem translations : Erdos675.HasTranslationProperty (Erdos675.composedOf leftPrimes) := by
  intro n
  let b := blocks n
  refine ⟨b.period,b.period_pos,?_⟩
  intro a ha ha'
  have hab : a ≤ b.base := ha'.trans (Nat.le_succ _ |>.trans b.pattern_le)
  have haIn : a ∈ Icc 1 (n+1) := mem_Icc.mpr ⟨ha,by omega⟩
  constructor
  · intro h
    refine ⟨by omega,fun p hprime hp => ?_⟩
    by_cases hsmall : p ≤ b.base
    · have hD := b.small_factor p hprime hsmall
      have hda : p ∣ a := by
        simpa using Nat.dvd_sub hp hD
      exact h.2 p hprime hda
    · exact Or.inl ⟨n,b.fresh_factor a haIn p hprime (lt_of_not_ge hsmall) hp⟩
  · intro h
    refine ⟨by omega,fun p hp hpa => ?_⟩
    have hbound : p ≤ b.base := (Nat.le_of_dvd ha hpa).trans hab
    exact h.2 p hp (dvd_add hpa (b.small_factor p hp hbound))

private theorem lower_bound_for_count {S : Set ℕ}
    (hs : ∀ᶠ x : ℕ in atTop, π x ≤ 8*(S ∩ Set.Iic x).ncard) :
    (fun x : ℕ => (x:ℝ)/log x) =O[atTop] fun x : ℕ => ((S ∩ Set.Iic x).ncard:ℝ) := by
  refine isBigO_iff.2 ⟨16,?_⟩
  filter_upwards [hs,prime_count_bounds,eventually_ge_atTop (2:ℕ)] with x hx hp h2
  have hlog : 0 < log (x:ℝ) := log_pos (by exact_mod_cast (show 1 < x by omega))
  have hc : (π x:ℝ) ≤ 8*((S ∩ Set.Iic x).ncard:ℝ) := by exact_mod_cast hx
  change |(x:ℝ)/log x| ≤ 16*|((S ∩ Set.Iic x).ncard:ℝ)|
  rw [abs_of_nonneg (show 0 ≤ (x:ℝ)/log x from div_nonneg (by positivity) hlog.le),
    abs_of_nonneg (show 0 ≤ ((S ∩ Set.Iic x).ncard:ℝ) by positivity)]
  have hdiv : (x:ℝ)/log x = 2*((x:ℝ)/(2*log x)) := by field_simp
  linarith [hp.1]

end OMA

theorem OMA.solution : type_of% @Erdos675.erdos_675.parts.ii := by
  exact ⟨OMA.leftPrimes, OMA.left_prime,
    OMA.lower_bound_for_count (OMA.both_counts.mono (fun _ h => h.1)),
    OMA.lower_bound_for_count (OMA.both_counts.mono (fun _ h => h.2)),
    OMA.translations⟩