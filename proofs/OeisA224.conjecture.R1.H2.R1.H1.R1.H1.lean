import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H1_R1

/-! Bound the normalized square-residue counts in each exponent range.
The last range at each prime includes every exponent above the cutoff. -/

namespace OMA.SmallPrimePair
open OeisA224
open OMA.R_OeisA224_conjecture_R1_H2_R1_H1_R1

private def cap (p : ℕ) := if p = 3 then 12 else if p < 11 then 7 else if p < 30 then 5 else 4
private def den (p : ℕ) := 2*(p+1)
private def correction (p j : ℕ) := if j % 2 = 0 then p+2 else 2*p+1
private def lower (p j : ℕ) := p*p^j + if j < cap p then correction p j else 0
private def upper (p j : ℕ) := p*p^j + if j < cap p then correction p j else 2*p+1
private def delta (p q j l : ℕ) := if j < cap p ∧ l < cap q then 1 else 0

private def checkCell (p q j l : ℕ) : Bool :=
  let D := den p * den q
  let M := p^j*q^l
  let L := lower p j * lower q l
  let U := upper p j * upper q l
  let b := delta p q j l
  let k := ((M^2-b)*D^2) / (L*(L-D))
  decide (D < L ∧ k * (U*(U-b*D)) < (M^2-1)*D^2)

private def primes := (List.range 201).filter fun p => decide (p.Prime ∧ Odd p)
private def rows (p q : ℕ) := (List.range (cap p+1)).all fun j =>
  (List.range (cap q+1)).all fun l =>
    decide (j = 0 ∨ l = 0 ∨ j+l < 3) || checkCell p q j l

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table : primes.all (fun p => primes.all (fun q => decide (q ≤ p) || rows p q)) = true := by
  decide +kernel

private theorem checked {p q j l : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p) (hqo : Odd q)
    (hpq : p < q) (hq' : q < 201) (hj : 0 < j) (hl : 0 < l) (hs : 3 ≤ j+l)
    (hj' : j ≤ cap p) (hl' : l ≤ cap q) : checkCell p q j l = true := by
  have hp' : p ∈ primes := by simp [primes, hp, hpo, hpq.trans hq']
  have hq'' : q ∈ primes := by simp [primes, hq, hqo, hq']
  have ht := List.all_eq_true.mp (List.all_eq_true.mp table p hp') q hq''
  have hr : rows p q = true := by simpa [not_le.mpr hpq] using ht
  have hjm : j ∈ List.range (cap p+1) := List.mem_range.mpr (by omega)
  have hlm : l ∈ List.range (cap q+1) := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp (List.all_eq_true.mp hr j hjm) l hlm
  simpa [hj.ne',hl.ne',Nat.not_lt.mpr hs] using hh

private theorem count_scaled {p : ℕ} (hp : p.Prime) (hpo : Odd p) (e : ℕ) :
    den p * a (p^e) = p*p^e + correction p e := by
  have hform := count_formula p hp hpo e
  have ha : 1 ≤ a (p^e) := by
    rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
    exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
  have hh : a (p^e) - 1 + 1 = a (p^e) := by omega
  rw [pow_succ] at hform
  dsimp [den, correction]
  by_cases hev : Even e <;> simp [hev, ← Nat.even_iff] at hform ⊢ <;>
    nlinarith only [hform, congrArg (fun z => 2*(p+1)*z) hh]

private theorem factor_bounds {p e : ℕ} (hp : p.Prime) (hpo : Odd p) :
    let j := min e (cap p)
    let t := p^(e-j)
    lower p j * t ≤ den p * a (p^e) ∧ den p * a (p^e) ≤ upper p j * t := by
  let j := min e (cap p)
  let t := p^(e-j)
  have hj : j ≤ e := min_le_left _ _
  have heq : p^e = p^j*t := by rw [← pow_add, Nat.add_sub_of_le hj]
  have ht : 1 ≤ t := pow_pos hp.pos _
  change lower p j * t ≤ _ ∧ _ ≤ upper p j * t
  rw [count_scaled hp hpo, heq]
  by_cases h : j < cap p
  · have hj' : j = e := by dsimp [j] at *; omega
    have ht' : t = 1 := by simp [t,hj']
    simp [lower,upper,hj',ht', hj' ▸ h]
  · have hc : correction p e ≤ 2*p+1 := by
      dsimp [correction]
      split <;> have := hp.two_le <;> omega
    simp only [lower,upper,if_neg h,add_zero]
    constructor
    · nlinarith
    · nlinarith only [hc, Nat.mul_le_mul_left (2*p+1) ht]

private theorem interval_excludes (M t D L U b A k : ℕ) (ht : 0 < t)
    (hb : b = 0 ∨ (b = 1 ∧ t = 1)) (hL : D < L)
    (hlo : L*t ≤ D*A) (hhi : D*A ≤ U*t)
    (cert : (((M^2-b)*D^2)/(L*(L-D))) * (U*(U-b*D)) < (M^2-1)*D^2)
    (eqn : (M*t)^2-1 = k*(A*(A-1))) : False := by
  have hbt : b*t ≤ 1 := by rcases hb with h|⟨h,r⟩ <;> simp_all
  have hbtt : b*t^2 ≤ 1 := by rcases hb with h|⟨h,r⟩ <;> simp_all
  have ht2 : 0 < t^2 := pow_pos ht _
  have hl' : (L-D)*t ≤ D*(A-1) := by
    rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_one]
    exact tsub_le_tsub hlo (Nat.le_mul_of_pos_right _ ht)
  have hu' : D*(A-1) ≤ (U-b*D)*t := by
    rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_one]
    apply tsub_le_tsub hhi
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.mul_le_mul_left D hbt)
  have hden : 0 < L*(L-D) := Nat.mul_pos (by omega) (by omega)
  have hnumlo : (M^2-1)*t^2 ≤ (M*t)^2-1 := by
    rw [Nat.sub_mul, one_mul, mul_pow]
    exact Nat.sub_le_sub_left ht2 _
  have hnumhi : (M*t)^2-1 ≤ (M^2-b)*t^2 := by
    rw [Nat.sub_mul, mul_pow]
    exact Nat.sub_le_sub_left hbtt _
  have hscale : D^2*((M*t)^2-1) = k*((D*A)*(D*(A-1))) := by rw [eqn]; ring
  have hklo : k*(L*(L-D)) ≤ (M^2-b)*D^2 := by
    apply Nat.le_of_mul_le_mul_right _ ht2
    calc
      _ = k*((L*t)*((L-D)*t)) := by ring
      _ ≤ k*((D*A)*(D*(A-1))) := Nat.mul_le_mul_left k (Nat.mul_le_mul hlo hl')
      _ = _ := hscale.symm
      _ ≤ D^2*((M^2-b)*t^2) := Nat.mul_le_mul_left _ hnumhi
      _ = _ := by ring
  have hkhi : (M^2-1)*D^2 ≤ k*(U*(U-b*D)) := by
    apply Nat.le_of_mul_le_mul_right _ ht2
    calc
      _ = D^2*((M^2-1)*t^2) := by ring
      _ ≤ D^2*((M*t)^2-1) := Nat.mul_le_mul_left _ hnumlo
      _ = _ := hscale
      _ ≤ k*((U*t)*((U-b*D)*t)) := Nat.mul_le_mul_left k (Nat.mul_le_mul hhi hu')
      _ = _ := by ring
  exact cert.not_ge (hkhi.trans (Nat.mul_le_mul_right _ ((Nat.le_div_iff_mul_le hden).mpr hklo)))

private theorem two_prime {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p)
    (hqo : Odd q) (hpq : p < q) (hq' : q < 201) (he : 0 < e) (hf : 0 < f)
    (hs : 3 ≤ e+f) : ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f)*(a (p^e*q^f)-1)] := by
  intro test
  let j := min e (cap p)
  let l := min f (cap q)
  let t := p^(e-j)
  let u := q^(f-l)
  have cp (x : ℕ) : 3 ≤ cap x := by unfold cap; split_ifs <;> decide
  have hjp : j ≤ cap p := min_le_right _ _
  have hlq : l ≤ cap q := min_le_right _ _
  have hc := checked hp hq hpo hqo hpq hq' (j:=j) (l:=l)
    (by dsimp [j]; have := cp p; omega) (by dsimp [l]; have := cp q; omega)
    (by dsimp [j,l]; have := cp p; have := cp q; omega) hjp hlq
  simp only [checkCell, decide_eq_true_eq] at hc
  obtain ⟨hL,cert⟩ := hc
  have hcop := (Nat.coprime_primes hp hq).mpr hpq.ne
  rw [OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (pow_pos hp.pos _) (pow_pos hq.pos _)
      ((hcop.pow_left _).pow_right _)] at test
  let A := a (p^e)*a (q^f)
  change (p^e*q^f)^2 ≡ 1 [MOD A*(A-1)] at test
  have h1 : 1 ≤ (p^e*q^f)^2 := pow_pos (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)) _
  obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' h1).mp test.symm
  have hpE : p^e = p^j*t := by rw [← pow_add, Nat.add_sub_of_le (min_le_left _ _)]
  have hqF : q^f = q^l*u := by rw [← pow_add, Nat.add_sub_of_le (min_le_left _ _)]
  have hN : p^e*q^f = (p^j*q^l)*(t*u) := by rw [hpE,hqF]; ring
  have hb : delta p q j l = 0 ∨ (delta p q j l = 1 ∧ t*u=1) := by
    dsimp [delta]
    split_ifs with h
    · have heq : j=e := by dsimp [j] at *; omega
      have hfq : l=f := by dsimp [l] at *; omega
      simp [t,u,heq,hfq]
    · simp
  obtain ⟨pl,pu⟩ := factor_bounds (e:=e) hp hpo
  obtain ⟨ql,qu⟩ := factor_bounds (e:=f) hq hqo
  change lower p j*t ≤ _ at pl
  change _ ≤ upper p j*t at pu
  change lower q l*u ≤ _ at ql
  change _ ≤ upper q l*u at qu
  apply interval_excludes (p^j*q^l) (t*u) (den p*den q) (lower p j*lower q l)
    (upper p j*upper q l) (delta p q j l) A k
    (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)) hb hL _ _ cert
  · rw [← hN, mul_comm k]; exact hk
  · simpa [A, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul pl ql
  · simpa [A, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul pu qu

end OMA.SmallPrimePair

open OMA.SmallPrimePair in
theorem OMA.solution : OMA.R_OeisA224_conjecture_R1_H2_R1_H1_R1.H1 := by
  intro p q e f hp hq hpo hqo hpq hq' he hf hs
  exact two_prime hp hq hpo hqo hpq hq' he hf hs
