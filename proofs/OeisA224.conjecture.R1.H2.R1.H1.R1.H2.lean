import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H1_R1

/-! Bound the normalized square-residue counts in each exponent range.
The last range at each prime includes every exponent above the cutoff. -/

namespace OMA.MixedPrimePair
open OeisA224
open OMA.R_OeisA224_conjecture_R1_H2_R1_H1_R1

private def cap (p : ℕ) := if p ≤ 5 then 12 else if p ≤ 11 then 9 else if p < 30 then 5 else 4
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
private def cutoff (p : ℕ) :=
  if p = 5 then 6401 else if p = 11 ∨ p = 31 then 3201 else
  if p = 3 ∨ p = 17 ∨ p = 29 then 801 else if p = 7 ∨ p = 37 ∨ p = 199 then 401 else 201

private def secondary (p c : ℕ) := if cutoff p ≤ max 201 (c*256) then [] else
  (List.range' (c*256) 256).filter fun q => decide (201 ≤ q ∧ q < cutoff p ∧ ¬ 2 ∣ q ∧ ¬ 3 ∣ q ∧ ¬ 5 ∣ q ∧ ¬ 7 ∣ q)
private def rows (p q : ℕ) := (List.range (cap p+1)).all fun j =>
  (List.range (cap q+1)).all fun l =>
    decide (j = 0 ∨ l = 0 ∨ j+l < 3) || checkCell p q j l

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table (c : ℕ) (hc : c < 26) :
    primes.all (fun p => (secondary p c).all (rows p)) = true := by
  interval_cases c <;> decide +kernel

private theorem checked {p q j l : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p)
    (hp' : p < 201) (hq0 : 201 ≤ q) (hq' : q < cutoff p) (hj : 0 < j) (hl : 0 < l) (hs : 3 ≤ j+l)
    (hj' : j ≤ cap p) (hl' : l ≤ cap q) : checkCell p q j l = true := by
  have hpm : p ∈ primes := by simp [primes, hp, hpo, hp']
  let c := q/256
  have hlo : c*256 ≤ q := Nat.div_mul_le_self _ _
  have hhi : q < c*256+256 := by dsimp [c]; omega
  have hh : ¬ cutoff p ≤ max 201 (c*256) := by omega
  have hm : q ∈ List.range' (c*256) 256 := by
    simpa using (show c*256 ≤ q ∧ q < c*256+256 from ⟨hlo,hhi⟩)
  have hnd (d : ℕ) (hd : 2 ≤ d) (hlt : d < 201) : ¬ d ∣ q := by
    rw [Nat.dvd_prime_two_le hq hd]
    omega
  have hqm : q ∈ secondary p c := by
    simp [secondary, hh, hm, hq0, hq', Nat.odd_iff.mp (hq.odd_of_ne_two (by omega)),
      hnd 3 (by decide) (by decide), hnd 5 (by decide) (by decide), hnd 7 (by decide) (by decide)]
  have hbound : cutoff p ≤ 6401 := by unfold cutoff; split_ifs <;> decide
  have hc : c < 26 := by dsimp [c]; omega
  have hr := List.all_eq_true.mp (List.all_eq_true.mp (table c hc) p hpm) q hqm
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

private theorem bounded_q {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p)
    (hqo : Odd q) (hp' : p < 201) (hq0 : 201 ≤ q) (hq' : q < cutoff p) (he : 0 < e) (hf : 0 < f)
    (hs : 3 ≤ e+f) : ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f)*(a (p^e*q^f)-1)] := by
  intro test
  let j := min e (cap p)
  let l := min f (cap q)
  let t := p^(e-j)
  let u := q^(f-l)
  have cp (x : ℕ) : 3 ≤ cap x := by unfold cap; split_ifs <;> decide
  have hjp : j ≤ cap p := min_le_right _ _
  have hlq : l ≤ cap q := min_le_right _ _
  have hc := checked hp hq hpo hp' hq0 hq' (j:=j) (l:=l)
    (by dsimp [j]; have := cp p; omega) (by dsimp [l]; have := cp q; omega)
    (by dsimp [j,l]; have := cp p; have := cp q; omega) hjp hlq
  simp only [checkCell, decide_eq_true_eq] at hc
  obtain ⟨hL,cert⟩ := hc
  have hcop := (Nat.coprime_primes hp hq).mpr (by omega)
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


private def tailCell (p j : ℕ) : Bool :=
  let Q := cutoff p
  let D := 2*den p
  let M := p^j*Q
  let L := lower p j*(Q-1)
  let U := upper p j*(Q+1)
  let k := M^2*D^2/(L*(L-D))
  decide (D < L ∧ (k*U^2 < (M^2-1)*D^2 ∨
    (p ∣ k ∧ (k-1)*U^2 < (M^2-1)*D^2)))

set_option maxRecDepth 100000 in
private theorem tailTable : primes.all (fun p =>
    (List.range (cap p+1)).all (fun j => decide (j=0) || tailCell p j)) = true := by decide +kernel

private theorem relative {p Q e : ℕ} (hp : p.Prime) (odd : Odd p) (hQ : 1 ≤ Q)
    (hle : Q ≤ p) (he : 0 < e) :
    (Q-1)*p^e ≤ 2*Q*a (p^e) ∧ 2*Q*a (p^e) ≤ (Q+1)*p^e := by
  let Y := p^e
  let A := a Y
  have hY : p ≤ Y := Nat.le_pow he
  have hf := count_scaled hp odd e
  change 2*(p+1)*A = p*Y + correction p e at hf
  have hmul := congrArg (Q * ·) hf
  have hc : correction p e ≤ 2*p+1 := by unfold correction; split <;> have := hp.two_le <;> omega
  have hc' : Q*correction p e ≤ (Q+p+1)*Y := calc
    _ ≤ Q*(2*p+1) := Nat.mul_le_mul_left _ hc
    _ ≤ (Q+p+1)*p := by nlinarith only [Nat.mul_le_mul_left (p+1) hle]
    _ ≤ _ := Nat.mul_le_mul_left _ hY
  change (Q-1)*Y ≤ 2*Q*A ∧ 2*Q*A ≤ (Q+1)*Y
  constructor
  · apply Nat.le_of_mul_le_mul_right _ (Nat.succ_pos p)
    have hfold : Q-1+1=Q := by omega
    nlinarith only [hmul, Nat.mul_le_mul_right Y hle,
      congrArg (fun z => z*Y*(p+1)) hfold, Nat.zero_le (Q*correction p e)]
  · apply Nat.le_of_mul_le_mul_right _ (Nat.succ_pos p)
    nlinarith only [hmul,hc']

private theorem tail_excludes (p M s Q D L U A N k : ℕ) (hs : Q ≤ s) (hs' : 0 < s)
    (hN : Q*N=M*s) (hL : D < L) (hlo : L*s ≤ (Q*D)*A) (hhi : (Q*D)*A ≤ U*s)
    (hprime : ¬ p ∣ k)
    (cert : let K := M^2*D^2/(L*(L-D))
      K*U^2 < (M^2-1)*D^2 ∨ (p ∣ K ∧ (K-1)*U^2 < (M^2-1)*D^2))
    (eqn : N^2-1=k*(A*(A-1))) : False := by
  let K := M^2*D^2/(L*(L-D))
  have hs2 := pow_pos hs' 2
  have hnum : Q^2*(N^2-1) = (M*s)^2-Q^2 := by rw [Nat.mul_sub, mul_one, ← mul_pow, hN]
  have hnumlo : (M^2-1)*s^2 ≤ Q^2*(N^2-1) := by
    rw [hnum, mul_pow, Nat.sub_mul, one_mul]
    exact Nat.sub_le_sub_left (Nat.pow_le_pow_left hs 2) _
  have hnumhi : Q^2*(N^2-1) ≤ M^2*s^2 := by rw [hnum, mul_pow]; exact Nat.sub_le _ _
  have hscale : D^2*(Q^2*(N^2-1)) = k*(((Q*D)*A)*((Q*D)*(A-1))) := by rw [eqn]; ring
  have hl' : (L-D)*s ≤ (Q*D)*(A-1) := by
    rw [Nat.sub_mul, Nat.mul_sub, mul_one]
    exact tsub_le_tsub hlo (by simpa [mul_comm] using Nat.mul_le_mul_left D hs)
  have hu' : (Q*D)*(A-1) ≤ U*s :=
    (Nat.mul_le_mul_left _ (Nat.sub_le A 1)).trans hhi
  have hk : k ≤ K := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mpr
    apply Nat.le_of_mul_le_mul_right _ hs2
    calc
      _ = k*((L*s)*((L-D)*s)) := by ring
      _ ≤ k*(((Q*D)*A)*((Q*D)*(A-1))) := Nat.mul_le_mul_left k (Nat.mul_le_mul hlo hl')
      _ = _ := hscale.symm
      _ ≤ D^2*(M^2*s^2) := Nat.mul_le_mul_left _ hnumhi
      _ = _ := by ring
  have hk' : (M^2-1)*D^2 ≤ k*U^2 := by
    apply Nat.le_of_mul_le_mul_right _ hs2
    calc
      _ = D^2*((M^2-1)*s^2) := by ring
      _ ≤ D^2*(Q^2*(N^2-1)) := Nat.mul_le_mul_left _ hnumlo
      _ = _ := hscale
      _ ≤ k*((U*s)*(U*s)) := Nat.mul_le_mul_left k (Nat.mul_le_mul hhi hu')
      _ = _ := by ring
  change K*U^2 < _ ∨ (p ∣ K ∧ (K-1)*U^2 < _) at cert
  rcases cert with hc|⟨hp,hc⟩
  · exact hc.not_ge (hk'.trans (Nat.mul_le_mul_right _ hk))
  · have hne : k ≠ K := fun h => hprime (h ▸ hp)
    exact hc.not_ge (hk'.trans (Nat.mul_le_mul_right _ (by omega)))

private theorem unbounded_q {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p)
    (hqo : Odd q) (hpq : p < q) (hp' : p < 201) (hq' : cutoff p ≤ q) (he : 0 < e) (hf : 0 < f) :
    ¬ (p^e*q^f)^2 ≡ 1 [MOD a (p^e*q^f)*(a (p^e*q^f)-1)] := by
  intro test
  let j := min e (cap p)
  let t := p^(e-j)
  let Y := q^f
  let Q := cutoff p
  let D := 2*den p
  let A := a (p^e)*a Y
  let N := p^e*Y
  have hQ : 1 ≤ Q := by dsimp [Q, cutoff]; split_ifs <;> decide
  have hcap : 0 < cap p := by unfold cap; split_ifs <;> decide
  have hj : 0 < j := lt_min he hcap
  have hpm : p ∈ primes := by simp [primes,hp,hpo,hp']
  have hjm : j ∈ List.range (cap p+1) := List.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _))
  have hc := List.all_eq_true.mp (List.all_eq_true.mp tailTable p hpm) j hjm
  simp only [hj.ne', decide_false, Bool.false_or, tailCell, decide_eq_true_eq] at hc
  have hcop := (Nat.coprime_primes hp hq).mpr hpq.ne
  rw [OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (pow_pos hp.pos _) (pow_pos hq.pos _)
      ((hcop.pow_left _).pow_right _)] at test
  change N^2 ≡ 1 [MOD A*(A-1)] at test
  have hN : 0 < N := Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
  have hn : 1 ≤ N^2 := pow_pos hN _
  obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' hn).mp test.symm
  have hpN : p ∣ N := dvd_mul_of_dvd_left (dvd_pow_self p he.ne') _
  have hpk : ¬ p ∣ k := by
    intro hpk
    have hk' : p ∣ N^2-1 := hk ▸ dvd_mul_of_dvd_right hpk _
    have hp2 : p ∣ N^2 := hpN.trans (dvd_pow_self _ (by decide))
    have hadd : (N^2-1)+1=N^2 := by omega
    exact hp.not_dvd_one ((Nat.dvd_add_right hk').mp (hadd ▸ hp2))
  have hE : p^e = p^j*t := by rw [← pow_add, Nat.add_sub_of_le (min_le_left _ _)]
  have hY : Q ≤ Y := hq'.trans (Nat.le_pow hf)
  have hs : Q ≤ t*Y := hY.trans (Nat.le_mul_of_pos_left _ (pow_pos hp.pos _))
  have hscale : Q*N = (p^j*Q)*(t*Y) := by dsimp only [N]; rw [hE]; ring
  obtain ⟨pl,pu⟩ := factor_bounds (e:=e) hp hpo
  change lower p j*t ≤ _ at pl
  change _ ≤ upper p j*t at pu
  obtain ⟨ql,qu⟩ := relative hq hqo hQ hq' hf
  change (Q-1)*Y ≤ 2*Q*a Y at ql
  change 2*Q*a Y ≤ (Q+1)*Y at qu
  exact tail_excludes p (p^j*Q) (t*Y) Q D (lower p j*(Q-1)) (upper p j*(Q+1)) A N k hs
    (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)) hscale hc.1
    (by simpa [D,A,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul pl ql)
    (by simpa [D,A,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul pu qu)
    hpk hc.2 (by simpa [Nat.mul_comm] using hk)

end OMA.MixedPrimePair

open OMA.MixedPrimePair in
theorem OMA.solution : OMA.R_OeisA224_conjecture_R1_H2_R1_H1_R1.H2 := by
  intro p q e f hp hq hpo hqo hpq hp' hq0 he hf hs
  rcases lt_or_ge q (cutoff p) with hq'|hq'
  · exact bounded_q hp hq hpo hqo hp' hq0 hq' he hf hs
  · exact unbounded_q hp hq hpo hqo hpq hp' hq' he hf
