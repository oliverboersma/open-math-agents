import OMAReductions.R_Erdos294_erdos_294_R1
import Mathlib

/-!
A finite Fourier extraction for the smooth-denominator representation in
Liu and Sawhney, arXiv:2404.07113, Section 4. Work modulo four times the
common denominator. The total possible sum is below the modulus, so a
congruence gives equality without a separate concentration inequality.
-/

open Finset Filter

namespace OMA.R_Erdos294_erdos_294_R1_H1_R1

/-- If no subset has the prescribed sum, the indicated Fourier coefficient
of the Bernoulli product vanishes. The parameter can even be complex. -/
theorem zero_of_no_subset {M : ℕ} [NeZero M] (A : Finset ℕ)
    (w : ℕ → ZMod M) (p : ℂ) (t : ZMod M) (no : ∀ B ⊆ A, (∑ n ∈ B,w n) ≠ t) :
    (∑ h : ZMod M, ZMod.stdAddChar ((-t)*h) *
      ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (w n*h))) = 0 := by
  classical
  induction A using Finset.induction_on generalizing t with
  | empty =>
    have ht : -t ≠ 0 := neg_ne_zero.mpr (fun ht => no ∅ (by simp) (by simp [ht]))
    simpa only [prod_empty,mul_one,AddChar.mulShift_apply] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M ht))
  | @insert i A hi ih =>
    have h₀ := ih t (fun B hB => no B (hB.trans (subset_insert _ _)))
    have h₁ := ih (t-w i) (fun B hB eq => by
      apply no (insert i B) (insert_subset_insert _ hB)
      rw [sum_insert (fun h => hi (hB h)), eq]
      abel)
    let F (h : ZMod M) : ℂ := ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (w n*h))
    calc
      _ = ∑ h : ZMod M, ((1-p)*(ZMod.stdAddChar ((-t)*h)*F h) +
          p*(ZMod.stdAddChar ((-(t-w i))*h)*F h)) := by
        apply sum_congr rfl
        intro h _
        rw [prod_insert hi,show (-(t-w i))*h = (-t)*h + w i*h by ring,
          AddChar.map_add_eq_mul]
        dsimp only [F]
        ring
      _ = _ := by rw [sum_add_distrib,←mul_sum,←mul_sum]; dsimp only [F]; rw [h₀,h₁];ring

/-- The central frequencies for an interval of Bernoulli reciprocals.
The choice of p centers the weighted sum at the requested numerator. -/
def H1 : Prop := ∀ᶠ N : ℕ in atTop, ∀ (Q : ℕ) [NeZero Q] (A : Finset ℕ),
  (∀ n ∈ A, 0<n ∧ N ≤ 16*n ∧ n ≤ N ∧ n ∣ Q) →
  3*Q ≤ 2*(∑ n ∈ A,Q/n) → (∑ n ∈ A,Q/n) ≤ 3*Q → ∀ t : ℕ, Q ≤ 3*t → t ≤ Q →
  let V := ∑ n ∈ A, Q/n
  let p : ℂ := (t:ℂ)/(V:ℂ)
  let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
  let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t : ZMod (4*Q)))*h) *
    ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (((Q/n : ℕ) : ZMod (4*Q))*h))
  1 ≤ (∑ h ∈ S, F h).re

/-- The arithmetic input is a set of smooth denominators with sufficient
mass and a bound for the complementary Fourier frequencies. -/
def H2 : Prop := ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  letI : NeZero Q := ⟨Nat.lcmUpto_ne_zero _⟩
  ∃ A : Finset ℕ, (∀ n ∈ A, 0<n ∧ N ≤ 16*n ∧ n ≤ N ∧ n ∣ Q) ∧
    3*Q ≤ 2*(∑ n ∈ A,Q/n) ∧ (∑ n ∈ A,Q/n) ≤ 3*Q ∧ ∀ t : ℕ, Q ≤ 3*t → t ≤ Q →
    let V := ∑ n ∈ A, Q/n
    let p : ℂ := (t:ℂ)/(V:ℂ)
    let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
    let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t : ZMod (4*Q)))*h) *
      ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (((Q/n : ℕ) : ZMod (4*Q))*h))
    ‖∑ h ∈ Sᶜ, F h‖ < 1

theorem main : H1 → H2 → OMA.R_Erdos294_erdos_294_R1.H1 := by
  classical
  rintro central ⟨c,hc,minor⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.1 (central.and minor)
  refine ⟨c,hc,N₀,?_⟩
  intro N hN d a hd hdiv ha₁ ha₂
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  have hQ : 0<Q := Nat.lcmUpto_pos _
  letI : NeZero Q := ⟨hQ.ne'⟩
  change d ∣ Q at hdiv
  obtain ⟨hcN,hmN⟩ := hN₀ N hN
  obtain ⟨A,hA,hmass,hcap,hminor⟩ := hmN
  let t := a*(Q/d)
  have htmax : t ≤ Q := calc
    _ ≤ d*(Q/d) := Nat.mul_le_mul_right _ ha₂
    _ = _ := Nat.mul_div_cancel' hdiv
  have htmin : Q ≤ 3*t := calc
    _ = d*(Q/d) := (Nat.mul_div_cancel' hdiv).symm
    _ ≤ (3*a)*(Q/d) := Nat.mul_le_mul_right _ ha₁
    _ = _ := by dsimp [t];ring
  let V := ∑ n ∈ A, Q/n
  let p : ℂ := (t:ℂ)/(V:ℂ)
  let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
  let w (n : ℕ) : ZMod (4*Q) := (Q/n:ℕ)
  let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t : ZMod (4*Q)))*h) *
    ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (w n*h))
  have hlow : 1 ≤ (∑ h ∈ S, F h).re := hcN Q A hA hmass hcap t htmin htmax
  have hhigh : ‖∑ h ∈ Sᶜ, F h‖ < 1 := hminor t htmin htmax
  have hnon : (∑ h, F h) ≠ 0 := by
    intro heq
    have hs := congrArg Complex.re ((Finset.sum_add_sum_compl S F).trans heq)
    rw [Complex.add_re,Complex.zero_re] at hs
    have hab := abs_le.mp (Complex.abs_re_le_norm (∑ h ∈ Sᶜ,F h))
    linarith
  obtain ⟨B,hB,hmod⟩ : ∃ B ⊆ A, (∑ n ∈ B,w n) = (t : ZMod (4*Q)) := by
    by_contra! no
    exact hnon (zero_of_no_subset A w p (t : ZMod (4*Q)) no)
  have hcast : ((∑ n ∈ B,Q/n : ℕ) : ZMod (4*Q)) = (t : ZMod (4*Q)) := by
    push_cast
    exact hmod
  have hsumle : (∑ n ∈ B,Q/n) ≤ 3*Q := (Finset.sum_le_sum_of_subset_of_nonneg hB
    (fun _ _ _ => Nat.zero_le _)).trans hcap
  have hsum := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hsum
  refine ⟨B,fun n hn => ⟨(hA n (hB hn)).2.1,(hA n (hB hn)).2.2.1⟩,?_⟩
  have hscale : (Q:ℚ)*(∑ n ∈ B,(1:ℚ)/n) = (t:ℚ) := by
    rw [← hsum, Nat.cast_sum, Finset.mul_sum]
    apply sum_congr rfl
    intro n hn
    obtain ⟨hnpos,_,_,hnQ⟩ := hA n (hB hn)
    have hm : ((Q/n:ℕ):ℚ)*n = Q := by exact_mod_cast Nat.div_mul_cancel hnQ
    rw [mul_one_div]
    exact (div_eq_iff (by exact_mod_cast hnpos.ne')).mpr hm.symm
  have ht : (t:ℚ)*d = (a:ℚ)*Q := by
    have hm : ((Q/d:ℕ):ℚ)*d = Q := by exact_mod_cast Nat.div_mul_cancel hdiv
    dsimp only [t]
    push_cast
    rw [mul_assoc,hm]
  apply (eq_div_iff (by exact_mod_cast hd.ne')).mpr
  apply mul_left_cancel₀ (by exact_mod_cast hQ.ne' : (Q:ℚ)≠0)
  rw [← mul_assoc,hscale,ht,mul_comm]

end OMA.R_Erdos294_erdos_294_R1_H1_R1
