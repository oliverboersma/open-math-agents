import OMAReductions.R_Erdos258_erdos_258_variants_monotone_R2
import Mathlib

/-! Based on Erdős and Straus, Some number theoretic results, Section 2.
Large bases allow a small first digit and a geometrically weighted divisor
tail. Small bases give a long constant interval on which congruences make
the initial digits integral. In either case a strictly positive remainder
less than one rules out an integral scaled tail. -/
namespace OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1

open Finset Filter Real
open OMA.R_Erdos258_erdos_258_variants_monotone_R2
open scoped Topology

/-- A typical divisor digit and a controlled weighted tail suffice at the
intermediate scale. This estimate only concerns the divisor function. -/
def H1 : Prop := ∀ q : ℕ, 0 < q → ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, X ≤ N ∧
  let L := (log X)^(7/8:ℝ)
  let G := ∑' k : ℕ, ((k+(N+1)+1).divisors.card:ℝ)/(2:ℝ)^k
  (q:ℝ)*((N+1).divisors.card+G/L) < L

/-- A congruence window in a long integer interval. Each initial divisor
digit is divisible by the appropriate power of the prescribed base. -/
def H2 : Prop := ∀ q : ℕ, 0 < q → ∀ᶠ X : ℕ in atTop, ∀ t : ℕ, 2 ≤ t →
  (t:ℝ) ≤ (log X)^(7/8:ℝ) → ∀ I : Finset ℕ, I ⊆ Icc 1 X →
  (∀ x ∈ I, ∀ y ∈ I, Icc x y ⊆ I) → X/⌊(log X)^(7/8:ℝ)⌋₊ ≤ I.card →
  ∃ N k : ℕ, Icc (N+1) (N+k) ⊆ I ∧ (∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) ∧
    (q:ℝ)*(∑' i : ℕ, ((i+(N+k)+1).divisors.card:ℝ)/(2:ℝ)^i) < (t:ℝ)^k

lemma prepare (a : ℕ → ℕ) (ha : ∀ n, 2 ≤ a n) :
    let T := fun n : ℕ => ((∏ i ∈ Icc 1 n, a i:ℕ):ℝ) *
      ∑' k, ((k+n+1).divisors.card:ℝ)/((∏ i ∈ Icc 1 (k+n+1), a i:ℕ):ℝ)
    let G := fun n : ℕ => ∑' k : ℕ, ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k
    (∀ n, 0 < T n) ∧ (∀ n, a (n+1)*T n = (n+1).divisors.card + T (n+1)) ∧
    ∀ n, T n*a (n+1) ≤ G n := by
  intro T G
  let pref := fun n : ℕ => ((∏ i ∈ Icc 1 n, a i:ℕ):ℝ)
  let raw := fun n : ℕ => ((n+1).divisors.card:ℝ)/pref (n+1)
  have ps (n : ℕ) : 0 < pref n := by dsimp [pref]; exact_mod_cast prod_pos a ha n
  have sm (n : ℕ) : Summable (fun k => raw (k+n)) := (summable_nat_add_iff n).mpr (summable_raw a ha)
  have step (n : ℕ) : pref (n+1) = pref n*a (n+1) := by
    dsimp [pref]
    rw [prod_split a (by omega : n ≤ n+1),Icc_self,prod_singleton,Nat.cast_mul]
  refine ⟨?_,?_,?_⟩
  · intro n
    exact mul_pos (ps n) ((sm n).tsum_pos (fun k => raw_nonneg a _) 0 (raw_pos a ha _))
  · intro n
    have eq := (sm n).tsum_eq_zero_add
    change (∑' k,raw (k+n)) = raw (0+n)+∑' k : ℕ, raw (k+1+n) at eq
    simp only [zero_add,Nat.add_right_comm _ 1 n] at eq
    change a (n+1)*(pref n * ∑' k,raw (k+n)) = _ + pref (n+1)*∑' k,raw (k+(n+1))
    rw [eq,mul_left_comm,←mul_assoc,←step,mul_add]
    simp only [Nat.add_assoc,raw]
    field_simp [(ps (n+1)).ne']
  · intro n
    have gsum : Summable (fun k : ℕ => ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k) := by
      have h₁ : Summable (fun k : ℕ => (k:ℝ)*((1:ℝ)/2)^k) := by
        simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1/2) (by norm_num)
      have h₂ := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).mul_left ((n:ℝ)+1)
      apply Summable.of_nonneg_of_le (fun k => by positivity) _ (h₁.add h₂)
      intro k
      change _ ≤ (k:ℝ)*(1/2:ℝ)^k+((n:ℝ)+1)*(1/2:ℝ)^k
      rw [←add_mul,div_pow,one_pow,mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh : ((k+n+1).divisors.card:ℝ) ≤ ((k+n+1:ℕ):ℝ) := by exact_mod_cast Nat.card_divisors_le_self _
      push_cast at hh
      linarith
    change (pref n*(∑' k,raw (k+n)))*a (n+1) ≤ _
    rw [mul_right_comm,←step,←tsum_mul_left]
    apply ((sm n).mul_left _).tsum_le_tsum _ gsum
    intro k
    let P := ∏ i ∈ Icc (n+1+1) (k+n+1), a i
    have fact : pref (k+n+1) = pref (n+1)*P := by
      dsimp [pref,P]; rw [prod_split a (by omega : n+1 ≤ k+n+1),Nat.cast_mul]
    have lower : 2^k ≤ P := calc
      _ = 2^(Icc (n+1+1) (k+n+1)).card := by rw [Nat.card_Icc]; congr 1; omega
      _ = ∏ _i ∈ Icc (n+1+1) (k+n+1),(2:ℕ) := (prod_const _).symm
      _ ≤ _ := Finset.prod_le_prod (by simp) (fun i _ => ha i)
    change pref (n+1)*((k+n+1).divisors.card/pref (k+n+1)) ≤ _
    rw [fact,←mul_div_assoc,mul_div_mul_left _ _ (ps _).ne']
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast lower)

private lemma integral_prefix (a : ℕ → ℕ) (T : ℕ → ℝ)
    (step : ∀ n, a (n+1)*T n = (n+1).divisors.card + T (n+1))
    (t N k : ℕ) (ht : 0 < t) (bases : ∀ j ∈ Icc 1 k, a (N+j) = t)
    (digits : ∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) :
    ∃ b : ℕ, T N = b+T (N+k)/(t:ℝ)^k := by
  induction k with
  | zero => exact ⟨0,by simp⟩
  | succ k ih =>
    have sub : Icc 1 k ⊆ Icc 1 (k+1) := fun j hj => mem_Icc.mpr ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans (by omega)⟩
    obtain ⟨b,hb⟩ := ih (fun j hj => bases j (sub hj)) (fun j hj => digits j (sub hj))
    have endmem : k+1 ∈ Icc 1 (k+1) := mem_Icc.mpr ⟨by omega,le_rfl⟩
    obtain ⟨c,hc⟩ := digits (k+1) endmem
    have eq := step (N+k)
    rw [Nat.add_assoc,bases _ endmem,hc,Nat.cast_mul,Nat.cast_pow] at eq
    refine ⟨b+c,?_⟩
    rw [hb,Nat.cast_add]
    have tp : (0:ℝ) < t := by exact_mod_cast ht
    rw [pow_succ] at eq ⊢
    have divEq : T (N+k)/(t:ℝ)^k = c + T (N+(k+1))/((t:ℝ)^k*t) := by
      field_simp [tp.ne']
      linear_combination eq
    rw [divEq]
    ring

theorem main : H1 → H2 → OMA.R_Erdos258_erdos_258_variants_monotone_R2.H2 := by
  intro typical window a ha mono _ _ q hq
  let T := fun n : ℕ => ((∏ i ∈ Icc 1 n, a i:ℕ):ℝ) *
      ∑' k, ((k+n+1).divisors.card:ℝ)/((∏ i ∈ Icc 1 (k+n+1), a i:ℕ):ℝ)
  let G := fun n : ℕ => ∑' k : ℕ, ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k
  let L := fun X : ℕ => (log X)^(7/8:ℝ)
  obtain ⟨pos,step,bound⟩ := prepare a ha
  change ∀ n, 0 < T n at pos
  change ∀ n, (a (n+1):ℝ)*T n = (n+1).divisors.card + T (n+1) at step
  change ∀ n, T n*a (n+1) ≤ G n at bound
  have qp : (0:ℝ)<q := by exact_mod_cast hq
  have ap (n : ℕ) : 1 ≤ (a n:ℝ) := by exact_mod_cast (show 1 ≤ a n by have := ha n; omega)
  by_cases fast : ∀ᶠ X : ℕ in atTop, L X ≤ a X
  · obtain ⟨X,fx,minX,N,XN,good⟩ := (fast.and ((eventually_gt_atTop (1:ℕ)).and (typical q hq))).exists
    change (q:ℝ)*((N+1).divisors.card+G (N+1)/L X)<L X at good
    have Lp : 0 < L X := Real.rpow_pos_of_pos (log_pos (by exact_mod_cast minX)) _
    have hbase (k : ℕ) (hk : X ≤ k) : L X ≤ a k := fx.trans (by exact_mod_cast mono hk)
    have hT : T (N+1) ≤ G (N+1)/L X := (le_div_iff₀ Lp).mpr <|
      (mul_le_mul_of_nonneg_left (hbase _ (by omega)) (pos _).le).trans (bound _)
    have lt : (q:ℝ)*T N < 1 := by
      have r := step N
      have H : (q:ℝ)*((a (N+1):ℝ)*T N) < a (N+1) := by
        rw [r]; apply lt_of_le_of_lt _ (good.trans_le (hbase _ (by omega)))
        exact mul_le_mul_of_nonneg_left (by linarith only [hT]) qp.le
      have posA : (0:ℝ) < a (N+1) := by linarith [ap (N+1)]
      apply (mul_lt_mul_iff_right₀ posA).mp
      linarith only [H]
    refine ⟨N,?_⟩
    rintro ⟨z,hz⟩
    change (z:ℝ) = q*T N at hz
    have zpos : (0:ℤ) < z := by exact_mod_cast (show (0:ℝ)<z by rw [hz]; exact mul_pos qp (pos N))
    have zsmall : z < (1:ℤ) := by exact_mod_cast (show (z:ℝ)<1 by rw [hz]; exact lt)
    omega
  · have often : ∃ᶠ X : ℕ in atTop, a X < L X := by
      simpa only [Filter.Frequently,not_lt] using fast
    obtain ⟨X,small,windows,Xlarge⟩ := (often.and_eventually ((window q hq).and
      ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (Real.exp 1)))).exists
    let h := ⌊L X⌋₊
    have Lp : 0 ≤ L X := (Nat.cast_nonneg _).trans small.le
    have ax : a X ≤ h := (Nat.le_floor_iff Lp).mpr small.le
    have hh : 1 ≤ h := by have := ha X; omega
    have map (i : ℕ) (hi : i ∈ Icc 1 X) : a i ∈ Icc 1 h := mem_Icc.mpr
      ⟨by have := ha i; omega,(mono (mem_Icc.mp hi).2).trans ax⟩
    have num : (Icc 1 h).card*(X/h) ≤ (Icc 1 X).card := by
      simp only [Nat.card_Icc]; simpa using Nat.mul_div_le X h
    obtain ⟨t,ht,hcount⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to (f := a) map
      (Finset.nonempty_Icc.mpr hh) num
    let I := (Icc 1 X).filter (fun n => a n=t)
    have Iin : I ⊆ Icc 1 X := filter_subset _ _
    have Xr : 0 < (X:ℝ) := (Real.exp_pos 1).trans Xlarge
    have lg : 1 ≤ log (X:ℝ) := (Real.le_log_iff_exp_le Xr).mpr Xlarge.le
    have Lbound : L X ≤ X := calc
      _ ≤ (log (X:ℝ))^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le lg (by norm_num)
      _ ≤ _ := by rw [Real.rpow_one]; linarith [Real.log_le_sub_one_of_pos Xr]
    have hX : h ≤ X := by exact_mod_cast ((Nat.floor_le Lp).trans Lbound : ((h:ℕ):ℝ)≤(X:ℝ))
    have has : I.Nonempty := Finset.card_pos.mp ((Nat.div_pos hX (by omega)).trans_le hcount)
    obtain ⟨i,hi⟩ := has
    have t2 : 2 ≤ t := (mem_filter.mp hi).2 ▸ ha i
    have convexI (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) : Icc i j ⊆ I := by
      intro k hk
      obtain ⟨ir,hit⟩ := mem_filter.mp hi
      obtain ⟨jr,hjt⟩ := mem_filter.mp hj
      obtain ⟨ik,kj⟩ := mem_Icc.mp hk
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ir).1.trans ik,kj.trans (mem_Icc.mp jr).2⟩,
        le_antisymm ((mono kj).trans_eq hjt) (hit.symm.le.trans (mono ik))⟩
    obtain ⟨N,k,rangeI,digits,cost⟩ := windows t t2 ((Nat.le_floor_iff Lp).mp (mem_Icc.mp ht).2)
      I Iin convexI hcount
    change (q:ℝ)*G (N+k) < (t:ℝ)^k at cost
    have base (j : ℕ) (hj : j ∈ Icc 1 k) : a (N+j)=t :=
      (mem_filter.mp (rangeI (mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega,
        Nat.add_le_add_left (mem_Icc.mp hj).2 N⟩))).2
    obtain ⟨b,eq⟩ := integral_prefix a T step t N k (by omega) base digits
    have qt : (q:ℝ)*T (N+k) < (t:ℝ)^k := by
      apply lt_of_le_of_lt _ cost
      apply mul_le_mul_of_nonneg_left _ qp.le
      have leProd : T (N+k) ≤ T (N+k)*a (N+k+1) := by
        simpa using (mul_le_mul_of_nonneg_left (ap (N+k+1)) (pos (N+k)).le)
      exact leProd.trans (bound _)
    have tk : 0 < (t:ℝ)^k := by
      have ht : 0 < (t:ℝ) := by exact_mod_cast (show 0<t by omega)
      positivity
    refine ⟨N,?_⟩
    rintro ⟨z,hz⟩
    change (z:ℝ) = q*T N at hz
    rw [eq,mul_add,←mul_div_assoc] at hz
    have l : 0 < (q:ℝ)*T (N+k)/(t:ℝ)^k := div_pos (mul_pos qp (pos _)) tk
    have u : (q:ℝ)*T (N+k)/(t:ℝ)^k < 1 := (div_lt_one tk).mpr qt
    have z₁ : (q:ℤ)*b < z := by exact_mod_cast (by linarith only [hz,l] : (q:ℝ)*b < z)
    have z₂ : z < (q:ℤ)*b+1 := by exact_mod_cast (by linarith only [hz,u] : (z:ℝ) < q*b+1)
    omega

end OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1
