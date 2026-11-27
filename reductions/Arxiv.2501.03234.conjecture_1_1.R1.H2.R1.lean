import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1

/-!
We use the floor-row identity and reflection formula of the parent reduction.
Even rows cancel. For an odd row a = 2k+1, each of the k differences of
adjacent floors costs at most p/a+1, so the signed row is at least p/a-a.
The total cost of the first L odd rows is at most 1+3+...+(2L-1) = L².
The remaining arithmetic question is a lower bound on the long-row tail.
-/
open Finset
namespace OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1
open OMA.R_Arxiv_2501_03234_conjecture_1_1_R1

/-- Square-block estimate for the odd harmonic sum. -/
def H1 : Prop := ∀ n L : ℕ, L ≤ n → n ≤ L^2 →
    ∑ k ∈ range n, (1 : ℚ)/(2*k+1) ≤ 2*∑ k ∈ range L, (1 : ℚ)/(2*k+1)

/-- Large odd rows cover the worst possible total rounding loss on the short ones. -/
def H2 : Prop := ∀ n : ℕ, (2*n+1).Prime → 100000 ≤ 2*n+1 →
    ((Nat.sqrt n + 1 : ℕ) : ℤ)^2 ≤ ∑ k ∈ Ico (Nat.sqrt n + 1) n,
      ∑ j ∈ Ico 1 (2*n+1), (-1 : ℤ)^((2*k+1)*j/(2*n+1))

lemma row_even (p a : ℕ) (hp : p.Prime) (ha : 0 < a) (hap : a < p)
    (he : Even a) : (∑ j ∈ Ico 1 p, (-1 : ℤ)^(a*j/p)) = 0 := by
  have aux (j : ℕ) (hj : j ∈ Ico 1 p) :
      (-1 : ℤ)^(a*(p-j)/p) = -((-1 : ℤ)^(a*j/p)) := by
    rcases mem_Ico.mp hj with ⟨hj1,hjp⟩
    have h := refl_aux p j a hp hj1 hjp ha hap
    rw [mul_comm (p-j) a, mul_comm j a] at h
    obtain ⟨b,hb⟩ := he
    have hpow : (-1 : ℤ)^(a*(p-j)/p) * (-1 : ℤ)^(a*j/p) = -1 := by
      rw [← pow_add, show a*(p-j)/p+a*j/p=2*(b-1)+1 by omega, pow_succ, pow_mul]
      norm_num
    rcases neg_one_pow_eq_or ℤ (a*j/p) with hh | hh <;> simp [hh] at hpow ⊢ <;> omega
  have href : (∑ j ∈ Ico 1 p, (-1 : ℤ)^(a*j/p)) = ∑ j ∈ Ico 1 p, (-1 : ℤ)^(a*(p-j)/p) := by
    rw [Finset.sum_Ico_reflect (fun j => (-1 : ℤ)^(a*j/p)) 1 (by omega)]
    congr 1
    ext j
    simp only [mem_Ico]
    omega
  have hneg := Finset.sum_congr (s₁:=Ico 1 p) (s₂:=Ico 1 p) rfl aux
  rw [Finset.sum_neg_distrib] at hneg
  change _ = -(∑ j ∈ Ico 1 p, (-1 : ℤ)^(a*j/p)) at hneg
  omega

lemma floor_gap (p a t : ℕ) (hp : 0 < p) (ha : 0 < a) :
    (((((t+2)*p-1)/a : ℕ) : ℚ) - ((((t+1)*p-1)/a : ℕ) : ℚ)) ≤ (p : ℚ)/a+1 := by
  let x := (t+1)*p-1
  have hnext : (t+2)*p-1=x+p := by
    dsimp [x]
    have h : (t+2)*p=(t+1)*p+p := by ring
    have hh : 0 < (t+1)*p := by positivity
    omega
  rw [hnext]
  have hfirst : a*((x+p)/a) ≤ x+p := by simpa [Nat.mul_comm] using Nat.div_mul_le_self (x+p) a
  have hlast : x < a*(x/a)+a := by
    have h := Nat.div_add_mod x a
    have h' := Nat.mod_lt x ha
    omega
  have hF : (a:ℚ)*(((x+p)/a : ℕ):ℚ) ≤ (x:ℚ)+p := by exact_mod_cast hfirst
  have hL : (x:ℚ) < (a:ℚ)*((x/a : ℕ):ℚ)+a := by exact_mod_cast hlast
  have ha' : (0:ℚ)<a := by exact_mod_cast ha
  rw [div_add_one (by positivity : (a:ℚ) ≠ 0), le_div_iff₀ ha']
  nlinarith

lemma pair_bound (p a k : ℕ) (hp : 0<p) (ha : 0<a) :
    ((∑ m ∈ Ico 1 (2*k+1), (-1:ℤ)^m * ((m*p-1)/a : ℕ) : ℤ) : ℚ)
      ≤ (k:ℚ)*((p:ℚ)/a+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1)+1=(2*k+1)+1+1 by ring, sum_Ico_succ_top (by omega),
      sum_Ico_succ_top (by omega)]
    rw [show 2*k+1+1=2*(k+1) by omega,
      show (-1:ℤ)^(2*k+1) = -1 by rw [pow_succ,pow_mul]; norm_num,
      show (-1:ℤ)^(2*(k+1)) = 1 by rw [pow_mul]; norm_num]
    simp only [Int.cast_add, Int.cast_neg, Int.cast_natCast, neg_one_mul, one_mul, Nat.cast_succ]
    have h := floor_gap p a (2*k) hp ha
    rw [show 2*k+2=2*(k+1) by omega] at h
    linarith only [ih,h]

lemma row_lower (p k : ℕ) (hp : 0<p) (ha : 2*k+1 < p) :
    (p:ℚ)/(2*k+1) - (2*k+1) ≤ ((∑ j ∈ Ico 1 p, (-1 : ℤ)^((2*k+1)*j/p) : ℤ) : ℚ) := by
  have h := inner_eq p (2*k+1) hp (by omega) ha
  change (∑ j ∈ Ico 1 p, (-1 : ℤ)^((2*k+1)*j/p)) = _ at h
  rw [show 2*k+1-1=2*k by omega, pow_mul] at h
  norm_num at h
  rw [h]
  push_cast
  have hb := pair_bound p (2*k+1) k hp (by omega)
  push_cast at hb
  have hdiv : ((p:ℚ)/(2*k+1))*(2*k+1)=p := div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma split_rows {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    ∑ a ∈ Ico 1 (2*n+1), f a =
      (∑ k ∈ range n, f (2*k+1)) + ∑ k ∈ range n, f (2*k+2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1=(2*n+1)+1+1 by ring, sum_Ico_succ_top (by omega),
      sum_Ico_succ_top (by omega), ih, sum_range_succ, sum_range_succ]
    ac_rfl

lemma odd_squares (L : ℕ) : ∑ k ∈ range L, ((2:ℚ)*k+1) = (L:ℚ)^2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ,ih]; push_cast; ring

theorem main : H1 → H2 → OMA.R_Arxiv_2501_03234_conjecture_1_1_R1.H2 := by
  intro hh ht p hp hbig
  obtain ⟨n,hn⟩ := hp.odd_of_ne_two (by omega)
  have hp' : p=2*n+1 := by omega
  clear hn
  subst p
  let L := Nat.sqrt n + 1
  have hL : L ≤ n := by
    have h := Nat.sqrt_lt' (m:=n) (n:=n)
    dsimp [L]
    have h2 : 2 ≤ n := by omega
    have : n < n^2 := by nlinarith [Nat.mul_le_mul_left n h2]
    exact h.mpr this
  have hsq : n ≤ L^2 := by
    exact (Nat.lt_succ_sqrt' n).le
  have hT := ht n hp hbig
  have hm := hh n L hL hsq
  have hM : ∑ a ∈ (Ico 1 (2*n+1)).filter Odd, ((2*n+1 : ℕ):ℚ)/a =
      ∑ k ∈ range n, ((2*n+1 : ℕ):ℚ)/(2*k+1) := by
    rw [Finset.sum_filter, split_rows]
    have odd1 (k : ℕ) : Odd (2*k+1) := ⟨k,rfl⟩
    have even2 (k : ℕ) : ¬ Odd (2*k+2) := by rintro ⟨t, ht⟩; omega
    simp [odd1,even2]
  have htot : Arxiv.«2501.03234».S (2*n+1) = ∑ k ∈ range n, (∑ j ∈ Ico 1 (2*n+1), (-1 : ℤ)^((2*k+1)*j/(2*n+1))) := by
    rw [S_eq _ hp]
    rw [split_rows]
    suffices (∑ k ∈ range n, (∑ j ∈ Ico 1 (2*n+1), (-1 : ℤ)^((2*k+2)*j/(2*n+1)))) = 0 by simp [this]
    apply sum_eq_zero
    intro k hk
    exact row_even _ _ hp (by omega) (by have := mem_range.mp hk; omega) ⟨k+1,by omega⟩
  rw [hM, ← S_eq_T _ hp ⟨n,by omega⟩, htot]
  let P : ℚ := ((2*n+1 : ℕ):ℚ)
  have hscale (t : ℕ) : P * (∑ k ∈ range t, (1:ℚ)/(2*k+1)) =
      ∑ k ∈ range t, P/(2*k+1) := by
    rw [mul_sum]
    simp only [div_eq_mul_inv, one_mul]
  have hscaled : ∑ k ∈ range n, P/(2*k+1) ≤ 2 * ∑ k ∈ range L, P/(2*k+1) := calc
    _ = P*(∑ k ∈ range n, (1:ℚ)/(2*k+1)) := (hscale n).symm
    _ ≤ P*(2*∑ k ∈ range L, (1:ℚ)/(2*k+1)) := mul_le_mul_of_nonneg_left hm (by dsimp [P]; positivity)
    _ = 2*(P*∑ k ∈ range L, (1:ℚ)/(2*k+1)) := by ring
    _ = _ := by rw [hscale]
  dsimp only [P] at hscaled
  have hsmall := sum_le_sum (s:=range L) (fun k hk =>
    row_lower (2*n+1) k (by omega) (by have := mem_range.mp hk; omega))
  rw [sum_sub_distrib, odd_squares] at hsmall
  have hr := sum_range_add_sum_Ico (f:=fun k => (∑ j ∈ Ico 1 (2*n+1), (-1 : ℤ)^((2*k+1)*j/(2*n+1)))) hL
  have htail : (L:ℚ)^2 ≤ ((∑ k ∈ Ico L n, (∑ j ∈ Ico 1 (2*n+1), (-1 : ℤ)^((2*k+1)*j/(2*n+1))) : ℤ):ℚ) := by exact_mod_cast hT
  push_cast at hr ⊢
  have hrq := congrArg (fun x : ℤ => (x:ℚ)) hr
  push_cast at hrq htail
  push_cast at hsmall hscaled ⊢
  linarith

end OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1
