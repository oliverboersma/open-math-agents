import OMAReductions.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1_H1_R1
import Mathlib

/-! Weighted lattice count for factorizations. Slice at the exponent of one
prime. The difference of two consecutive powers bounds each slice from
both sides, giving the inner and outer simplex estimates by telescoping. -/
namespace SmoothSimplex710

open Finset Real

noncomputable def cut (P : Finset ℕ) (v : ℝ) : Finset ℕ :=
  (range (⌊exp v⌋₊+1)).filter (· ∈ Nat.factoredNumbers P)

private lemma cut_mem {P : Finset ℕ} {v : ℝ} {n : ℕ} :
    n ∈ cut P v ↔ n ∈ Nat.factoredNumbers P ∧ log n ≤ v := by
  simp only [cut,mem_filter,mem_range_succ_iff]
  constructor
  · rintro ⟨hn,hp⟩
    have hpos : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers hp)
    exact ⟨hp,(Real.log_le_iff_le_exp hpos).mpr ((Nat.le_floor_iff (exp_pos _).le).mp hn)⟩
  · rintro ⟨hp,hn⟩
    have hpos : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers hp)
    exact ⟨(Nat.le_floor_iff (exp_pos _).le).mpr ((Real.log_le_iff_le_exp hpos).mp hn),hp⟩

private lemma split_count (P : Finset ℕ) (p : ℕ) (hp : p.Prime) (fresh : p ∉ P)
    (v : ℝ) (hv : 0 ≤ v) :
    (cut (insert p P) v).card =
      ∑ j ∈ range (⌊v/log p⌋₊+1), (cut P (v-j*log p)).card := by
  classical
  let E := Nat.equivProdNatFactoredNumbers hp fresh
  have pp : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have a : 0 < log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have logprod (j n : ℕ) (hn : n ∈ Nat.factoredNumbers P) :
      log ((p^j*n:ℕ):ℝ) = j*log p+log n := by
    have hnp : 0 < n := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers hn)
    push_cast
    rw [Real.log_mul (pow_ne_zero _ pp.ne') (by exact_mod_cast hnp.ne'), Real.log_pow]
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_bij (fun z _ => p^z.1*z.2)
  · intro z hz
    obtain ⟨_,hn⟩ := mem_sigma.mp hz
    obtain ⟨hn,hl⟩ := cut_mem.mp hn
    apply cut_mem.mpr
    exact ⟨(E (z.1,⟨z.2,hn⟩)).property,by rw [logprod _ _ hn]; linarith⟩
  · rintro ⟨i,m⟩ hx ⟨j,n⟩ hy he
    have hm := (cut_mem.mp (mem_sigma.mp hx).2).1
    have hn := (cut_mem.mp (mem_sigma.mp hy).2).1
    have same : ((i,⟨m,hm⟩) : ℕ × Nat.factoredNumbers P) = (j,⟨n,hn⟩) :=
      E.injective (Subtype.ext he)
    simpa using congrArg (fun t : ℕ × Nat.factoredNumbers P => Sigma.mk (β := fun _ : ℕ => ℕ) t.1 t.2.val) same
  · intro x hx
    obtain ⟨hx,hl⟩ := cut_mem.mp hx
    obtain ⟨⟨j,⟨n,hn⟩⟩,he⟩ := E.surjective ⟨x,hx⟩
    have hx' : p^j*n = x := congrArg Subtype.val he
    rw [←hx',logprod j n hn] at hl
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers hn)
    have hnlog : 0 ≤ log n := Real.log_nonneg (by exact_mod_cast hn1)
    refine ⟨⟨j,n⟩,mem_sigma.mpr ⟨mem_range_succ_iff.mpr ?_,cut_mem.mpr ⟨hn,by linarith⟩⟩,hx'⟩
    exact (Nat.le_floor_iff (div_nonneg hv a.le)).mpr ((le_div_iff₀ a).mpr (by linarith))

private lemma increment (d : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (d+1:ℕ)*(y-x)*x^d ≤ y^(d+1)-x^(d+1) ∧
    y^(d+1)-x^(d+1) ≤ (d+1:ℕ)*(y-x)*y^d := by
  let g := ∑ i ∈ range (d+1), y^i*x^(d-i)
  have hg : g*(y-x) = y^(d+1)-x^(d+1) := by simpa [g] using geom_sum₂_mul y x (d+1)
  have low : (d+1:ℕ)*x^d ≤ g := calc
    _ = ∑ _i ∈ range (d+1), x^d := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      have hd := mem_range_succ_iff.mp hi
      calc
        x^d = x^i*x^(d-i) := by rw [←pow_add,Nat.add_sub_of_le hd]
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (pow_nonneg hx _)
  have hi : g ≤ (d+1:ℕ)*y^d := calc
    _ ≤ ∑ _i ∈ range (d+1), y^d := by
      apply sum_le_sum
      intro i hi
      have hd := mem_range_succ_iff.mp hi
      calc
        _ ≤ y^i*y^(d-i) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) (pow_nonneg (hx.trans hxy) _)
        _ = _ := by rw [←pow_add,Nat.add_sub_of_le hd]
    _ = _ := by simp
  have h₁ := mul_le_mul_of_nonneg_right low (sub_nonneg.mpr hxy)
  have h₂ := mul_le_mul_of_nonneg_right hi (sub_nonneg.mpr hxy)
  constructor <;> linarith only [hg,h₁,h₂]

private lemma slices (d : ℕ) (v a t : ℝ) (hv : 0 ≤ v) (ha : 0 < a) (ht : 0 ≤ t) :
    let N := ⌊v/a⌋₊+1
    v^(d+1) ≤ ((d+1:ℕ)*a)*∑ i ∈ range N, (v-i*a)^d ∧
    ((d+1:ℕ)*a)*∑ i ∈ range N, (v-i*a+t)^d ≤ (v+t+a)^(d+1) := by
  intro N
  have left (i : ℕ) (hi : i ∈ range N) : 0 ≤ v-i*a := by
    have hi' := (Nat.le_floor_iff (div_nonneg hv ha.le)).mp (mem_range_succ_iff.mp hi)
    exact sub_nonneg.mpr ((le_div_iff₀ ha).mp hi')
  have last : v ≤ (N:ℝ)*a := by
    have h := (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one (v/a))
    simpa [N] using h.le
  let low := fun i : ℕ => (max (v-i*a) 0)^(d+1)
  let high := fun i : ℕ => (v-i*a+t+a)^(d+1)
  have low0 : low 0 = v^(d+1) := by simp [low,max_eq_left hv]
  have lowN : low N = 0 := by simp [low,max_eq_right (sub_nonpos.mpr last)]
  have high0 : high 0 = (v+t+a)^(d+1) := by simp [high]
  have hN : 0 ≤ v-(N:ℝ)*a+t+a := by
    have hh := (le_div_iff₀ ha).mp (Nat.floor_le (div_nonneg hv ha.le))
    dsimp [N]; push_cast; linarith
  have dp : 0 ≤ ((d+1:ℕ):ℝ) := by positivity
  constructor
  · have h : ∑ i ∈ range N, (low i-low (i+1)) ≤
        ∑ i ∈ range N, ((d+1:ℕ)*a)*(v-i*a)^d := by
      apply sum_le_sum
      intro i hi
      let x := v-i*a
      have hx : 0 ≤ x := left i hi
      have hj : max (x-a) 0 ≤ x := max_le (by linarith) hx
      have inc := (increment d (max (x-a) 0) x (le_max_right _ _) hj).2
      have hh : x-max (x-a) 0 ≤ a := by linarith [le_max_left (x-a) 0]
      have cap := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh dp) (pow_nonneg hx d)
      have step : v-((i+1:ℕ):ℝ)*a = x-a := by dsimp [x]; push_cast; ring
      change (max x 0)^(d+1)-(max (v-((i+1:ℕ):ℝ)*a) 0)^(d+1) ≤ _
      rw [max_eq_left hx,step]
      exact inc.trans cap
    rw [Finset.sum_range_sub',low0,lowN,sub_zero,←Finset.mul_sum] at h
    exact h
  · have h : ∑ i ∈ range N, ((d+1:ℕ)*a)*(v-i*a+t)^d ≤
        ∑ i ∈ range N, (high i-high (i+1)) := by
      apply sum_le_sum
      intro i hi
      let x := v-i*a+t
      have hx : 0 ≤ x := add_nonneg (left i hi) ht
      have inc := (increment d x (x+a) hx (by linarith)).1
      have step : v-((i+1:ℕ):ℝ)*a+t+a = x := by dsimp [x]; push_cast; ring
      change _ ≤ (x+a)^(d+1)-(v-((i+1:ℕ):ℝ)*a+t+a)^(d+1)
      rw [step]; simpa only [add_sub_cancel_left] using inc
    rw [Finset.sum_range_sub',high0,←Finset.mul_sum] at h
    exact h.trans (sub_le_self _ (pow_nonneg hN _))

private lemma estimates (P : Finset ℕ) (primes : ∀ p ∈ P, Nat.Prime p) (v : ℝ) (hv : 0 ≤ v) :
    let D := (P.card.factorial:ℝ) * ∏ p ∈ P, log (p:ℝ)
    let t := ∑ p ∈ P, log (p:ℝ)
    v^P.card ≤ (cut P v).card*D ∧ (cut P v).card*D ≤ (v+t)^P.card := by
  classical
  induction P using Finset.induction_on generalizing v with
  | empty =>
    have emp : cut ∅ v = {1} := by
      ext n
      simp only [cut_mem,Nat.factoredNumbers_empty,Set.mem_singleton_iff,Finset.mem_singleton]
      constructor
      · exact And.left
      · rintro rfl
        exact ⟨rfl,by simpa using hv⟩
    simp [emp]
  | @insert p P fresh ih =>
    have hp := primes p (mem_insert_self _ _)
    have rest : ∀ q ∈ P, Nat.Prime q := fun q hq => primes q (mem_insert_of_mem hq)
    let d := P.card
    let a := log (p:ℝ)
    let T := ∑ q ∈ P, log (q:ℝ)
    let D := (d.factorial:ℝ)*∏ q ∈ P, log (q:ℝ)
    let N := ⌊v/a⌋₊+1
    have ap : 0 < a := log_pos (by exact_mod_cast hp.one_lt)
    have tp : 0 ≤ T := sum_nonneg fun q hq => log_nonneg (by exact_mod_cast (rest q hq).one_le)
    have coeff : 0 ≤ ((d+1:ℕ):ℝ)*a := by positivity
    have count : ((cut (insert p P) v).card:ℝ) = ∑ j ∈ range N, ((cut P (v-j*a)).card:ℝ) := by
      exact_mod_cast split_count P p hp fresh v hv
    have lower (j : ℕ) (hj : j ∈ range N) : 0 ≤ v-j*a := by
      have H := (Nat.le_floor_iff (div_nonneg hv ap.le)).mp (mem_range_succ_iff.mp hj)
      exact sub_nonneg.mpr ((le_div_iff₀ ap).mp H)
    have s₁ : (∑ j ∈ range N, (v-j*a)^d) ≤ (cut (insert p P) v).card*D := by
      rw [count,Finset.sum_mul]
      exact sum_le_sum fun j hj => (ih rest _ (lower j hj)).1
    have s₂ : (cut (insert p P) v).card*D ≤ ∑ j ∈ range N, (v-j*a+T)^d := by
      rw [count,Finset.sum_mul]
      exact sum_le_sum fun j hj => (ih rest _ (lower j hj)).2
    obtain ⟨lo,hi⟩ := slices d v a T hv ap tp
    change v^(d+1) ≤ ((d+1:ℕ)*a)*∑ j ∈ range N, (v-j*a)^d at lo
    change ((d+1:ℕ)*a)*∑ j ∈ range N, (v-j*a+T)^d ≤ (v+T+a)^(d+1) at hi
    have den : ((d+1).factorial:ℝ)*(log (p:ℝ)*∏ q ∈ P, log (q:ℝ)) = ((d+1:ℕ)*a)*D := by
      dsimp [D,a]; rw [Nat.factorial_succ,Nat.cast_mul]; ring
    simp only [card_insert_of_notMem fresh,prod_insert fresh,sum_insert fresh]
    change v^(d+1) ≤ (cut (insert p P) v).card * _ ∧
      (cut (insert p P) v).card * _ ≤ (v+(a+T))^(d+1)
    rw [den]
    constructor
    · apply lo.trans
      convert mul_le_mul_of_nonneg_left s₁ coeff using 1 <;> ring
    · apply le_trans _ (show ((d+1:ℕ)*a)*∑ j ∈ range N, (v-j*a+T)^d ≤ (v+(a+T))^(d+1)
          by convert hi using 1 <;> ring)
      convert mul_le_mul_of_nonneg_left s₂ coeff using 1 <;> ring

lemma smooth_estimate (y : ℕ) (hy : 3 ≤ y) : ∃ C : ℝ, ∀ v : ℝ, 1 ≤ v →
    let d := (y.primesBelow.card:ℝ)
    let f := log ((Nat.smoothNumbersUpTo ⌊exp v⌋₊ y).card:ℝ)
    C+d*log v ≤ f ∧ f ≤ C+d*log (v+d*log y) := by
  let P := y.primesBelow
  let d := P.card
  let D := (d.factorial:ℝ)*∏ p ∈ P, log (p:ℝ)
  let T := ∑ p ∈ P, log (p:ℝ)
  have primes : ∀ p ∈ P, Nat.Prime p := fun p hp => Nat.prime_of_mem_primesBelow hp
  have positive (p : ℕ) (hp : p ∈ P) : 0 < log (p:ℝ) := log_pos (by exact_mod_cast (primes p hp).one_lt)
  have Dpos : 0 < D := mul_pos (by exact_mod_cast Nat.factorial_pos d) (Finset.prod_pos positive)
  have Tpos : 0 ≤ T := sum_nonneg fun p hp => (positive p hp).le
  have Tle : T ≤ (d:ℝ)*log y := calc
    _ ≤ ∑ _p ∈ P, log (y:ℝ) := sum_le_sum fun p hp =>
      log_le_log (by exact_mod_cast (primes p hp).pos) (by exact_mod_cast (Nat.lt_of_mem_primesBelow hp).le)
    _ = _ := by simp [d]
  refine ⟨-log D,?_⟩
  intro v hv
  have vp : 0 < v := by linarith
  have setEq : Nat.smoothNumbersUpTo ⌊exp v⌋₊ y = cut P v := by
    simp only [Nat.smoothNumbersUpTo,cut,Nat.smoothNumbers_eq_factoredNumbers_primesBelow,P]
  rw [setEq]
  let B := ((cut P v).card:ℝ)
  have Bpos : 0 < B := by
    dsimp [B]
    exact_mod_cast (Finset.card_pos.mpr ⟨1,cut_mem.mpr ⟨by simp [Nat.mem_factoredNumbers],by simpa using vp.le⟩⟩ :
      0 < (cut P v).card)
  obtain ⟨low,high⟩ := estimates P primes v vp.le
  change v^d ≤ B*D at low
  change B*D ≤ (v+T)^d at high
  have high' := high.trans (pow_le_pow_left₀ (by linarith : 0 ≤ v+T) (by linarith only [Tle] : v+T ≤ v+(d:ℝ)*log y) d)
  have l := Real.log_le_log (pow_pos vp _) low
  have h := Real.log_le_log (mul_pos Bpos Dpos) high'
  rw [Real.log_mul Bpos.ne' Dpos.ne',Real.log_pow] at l h
  change -log D + (d:ℝ)*log v ≤ log B ∧ log B ≤ -log D + (d:ℝ)*log (v+(d:ℝ)*log y)
  constructor <;> linarith only [l,h]

end SmoothSimplex710

theorem OMA.solution : OMA.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1_H1_R1.H1 := SmoothSimplex710.smooth_estimate
