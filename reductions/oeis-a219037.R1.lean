import OMAStatements.S_oeis_a219037

/-! Forward and backward exponent descent for A219037. -/

open OMA.S_oeis_a219037

namespace OMA.R_oeis_a219037_R1

private lemma exponent_dvd {s e : ℕ} (hs : 0 < s) (_he : 0 < e)
    (h : 2^s+1 ∣ 2^e+1) : s ∣ e := by
  have factor (j : ℕ) : 2^j+1 ∣ 2^(2*j)-1 := by
    refine ⟨2^j-1, ?_⟩
    have hp : 0 < 2^j := by positivity
    have heq : 2^j-1+1 = 2^j := by omega
    rw [pow_mul']
    have pos := pow_pos hp 2
    have diff := Nat.sub_add_cancel (show 1 ≤ (2^j)^2 by omega)
    nlinarith only [diff,heq,congrArg (fun x : ℕ => x*(2^j-1+1)) heq,congrArg (fun x : ℕ => 2^j*x) heq]
  have hd := Nat.dvd_gcd (factor s) (h.trans (factor e))
  rw [Nat.pow_sub_one_gcd_pow_sub_one,Nat.gcd_mul_left] at hd
  by_contra hn
  have hg := Nat.gcd_dvd_left s e
  have hne : s.gcd e ≠ s := fun eq => hn (eq ▸ Nat.gcd_dvd_right s e)
  obtain ⟨v,hv⟩ := hg
  have hv2 : 2 ≤ v := by
    by_contra! hlow
    interval_cases v <;> simp only [Nat.mul_zero,Nat.mul_one] at hv <;> omega
  have small : 2*s.gcd e ≤ s := by nlinarith [Nat.mul_le_mul_left (s.gcd e) hv2]
  have bound := Nat.pow_le_pow_right (by decide : 0 < 2) small
  have gp := Nat.gcd_pos_of_pos_left e hs
  have large := Nat.le_of_dvd (show 0 < 2^(2*s.gcd e)-1 by
    have := (2*s.gcd e).lt_two_pow_self; omega) hd
  exact Nat.not_succ_le_self _ (large.trans ((Nat.sub_le _ 1).trans bound))

private lemma odd_lift {s e : ℕ} (h : s ∣ e) (ho : Odd (e/s)) :
    2^s+1 ∣ 2^e+1 := by
  have eq := Nat.div_mul_cancel h
  simpa only [one_pow,←pow_mul,Nat.mul_comm s (e/s),eq] using
    (ho.nat_add_dvd_pow_add_pow (x := 2^s) (y := 1))

private lemma term_shape {k : ℕ} (h : IsTerm k) : 2 ≤ k ∧ k % 4 = 2 := by
  obtain ⟨h1,h2⟩ := h
  have hk : 2 ≤ k := by
    by_contra! h
    interval_cases k <;> norm_num at *
  obtain ⟨t,rt⟩ := Nat.exists_eq_add_of_le' hk
  have four : 2^k = 4*2^t := by rw [rt,pow_add]; ring
  have even : k%2 = 0 := by
    by_contra hh
    have dv : 2 ∣ k-1 := by omega
    have := dv.trans h2
    omega
  by_contra hh
  have dv : 4 ∣ k := by omega
  have := dv.trans h1
  omega

private lemma term_forward {k : ℕ} (h : IsTerm k) : IsTerm (2^k+2) := by
  obtain ⟨hk,hmod⟩ := term_shape h
  have hk1 : k-1+1=k := by omega
  have poweq : 2^k=2*2^(k-1) := by nth_rw 1 [←hk1]; rw [pow_succ]; ring
  obtain ⟨a,ha⟩ := h.1
  obtain ⟨b,hb⟩ := h.2
  have hm : 4 ∣ 2^k := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact ⟨2^j, by rw [pow_add]; ring⟩
  have oa : Odd a := by
    rw [Nat.odd_iff]
    have am := Nat.mod_lt a (by decide : 0 < 4)
    have hh := congrArg (·%4) ha
    rw [Nat.mul_mod,hmod] at hh
    interval_cases r : a%4 <;> simp at hh <;> omega
  have ob : Odd b := by
    rw [Nat.odd_iff]
    have kb : (k-1)%2=1 := by omega
    have hh := congrArg (·%2) hb
    rw [Nat.mul_mod,kb,one_mul,Nat.mod_mod] at hh
    omega
  have liftA := odd_lift h.1 (show Odd ((2^k+2)/k) by simpa [ha,Nat.ne_of_gt (by omega : 0 < k)] using oa)
  have liftB := odd_lift h.2 (show Odd ((2^k+1)/(k-1)) by simpa [hb,Nat.ne_of_gt (by omega : 0 < k-1)] using ob)
  constructor
  · obtain ⟨c,hc⟩ := liftB
    use c
    rw [show 2^k+2=(2^k+1)+1 by omega,pow_succ]
    nlinarith only [hc,poweq]
  · simpa using liftA

private lemma term_backward {s : ℕ} (hs : 2 ≤ s) (h : IsTerm (2^s+2)) : IsTerm s := by
  have heq : 2^s=2*2^(s-1) := by
    nth_rw 1 [show s=s-1+1 by omega]; rw [pow_succ]; ring
  obtain ⟨c,hc⟩ := h.1
  have hd : 2^(s-1)+1 ∣ 2^(2^s+1)+1 := by
    refine ⟨c, ?_⟩
    rw [show 2^s+2=(2^s+1)+1 by omega,pow_succ] at hc
    nlinarith only [hc,heq]
  exact ⟨exponent_dvd (by omega) (by positivity) (by simpa using h.2),
    exponent_dvd (by omega) (by positivity) hd⟩

private lemma frobenius_iter {p : ℕ} (hp : p.Prime) (a : ℕ) : 2^(p^a) ≡ 2 [MOD p] := by
  have flt : 2^p ≡ 2 [MOD p] := by
    rw [←Int.natCast_modEq_iff, Nat.cast_pow]
    exact Int.ModEq.pow_prime_eq_self hp 2
  induction a with
  | zero => simp only [pow_zero,pow_one]; rfl
  | succ a ih =>
    rw [pow_succ,pow_mul]
    exact (ih.pow p).trans flt

private lemma small_obstructions {k : ℕ} (h : IsTerm k) : ¬18 ∣ k ∧ ¬25 ∣ k-1 := by
  obtain ⟨hk,h4⟩ := term_shape h
  constructor
  · rintro ⟨v,hv⟩
    have div : 9 ∣ 2^k+2 := (show 9 ∣ k by omega).trans h.1
    have mod : 2^(18*v) ≡ 1 [MOD 9] := by
      rw [pow_mul]
      simpa using (show 2^18 ≡ 1 [MOD 9] by decide).pow v
    rw [hv] at div
    have bad := ((mod.add_right 2).symm.trans (Nat.modEq_zero_iff_dvd.mpr div))
    exact (by decide : ¬3 ≡ 0 [MOD 9]) bad
  · intro dv
    have div := dv.trans h.2
    have eq : k=20*(k/20)+6 := by omega
    have mod : 2^k ≡ 64 [MOD 25] := by
      conv_lhs => rw [eq,pow_add,pow_mul]
      change (2^20)^(k/20)*64 ≡ 64 [MOD 25]
      simpa only [one_pow,one_mul] using (((show 2^20 ≡ 1 [MOD 25] by decide).pow (k/20)).mul_right 64)
    have bad := ((mod.add_right 1).symm.trans (Nat.modEq_zero_iff_dvd.mpr div))
    exact (by decide : ¬65 ≡ 0 [MOD 25]) bad

private lemma neither_prime_power {k : ℕ} (h : IsTerm k) (hk : 6 < k) :
    (∀ p a : ℕ, p.Prime → k ≠ 2*p^a) ∧ (∀ p a : ℕ, p.Prime → k ≠ p^a+1) := by
  obtain ⟨_,h4⟩ := term_shape h
  obtain ⟨h18,h25⟩ := small_obstructions h
  constructor
  · intro p a hp heq
    have ha : 0 < a := by by_contra! hh; simp [show a=0 by omega] at heq; omega
    have dp : p ∣ k := heq ▸ dvd_mul_of_dvd_right (dvd_pow_self p ha.ne') 2
    have div := dp.trans h.1
    have mod : 2^k ≡ 4 [MOD p] := by
      rw [heq,pow_mul']
      exact (frobenius_iter hp a).pow 2
    have six : p ∣ 6 := Nat.modEq_zero_iff_dvd.mp ((mod.add_right 2).symm.trans (Nat.modEq_zero_iff_dvd.mpr div))
    have hp3 : p=3 := by
      have cases := hp.dvd_mul.mp (show p ∣ 2*3 from six)
      rcases cases with l | r
      · have eq := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp l
        subst p
        exact False.elim (by have dv := dvd_pow_self 2 ha.ne'; omega)
      · exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp r
    subst p
    have a2 : 2 ≤ a := by by_contra! hh; interval_cases a <;> simp_all
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le' a2
    rw [heq,pow_add] at h18
    exact h18 ⟨3^b,by ring⟩
  · intro p a hp heq
    have ha : 0 < a := by by_contra! hh; simp [show a=0 by omega] at heq; omega
    have dp : p ∣ k-1 := by rw [heq,Nat.add_sub_cancel]; exact dvd_pow_self p ha.ne'
    have div := dp.trans h.2
    have mod : 2^k ≡ 4 [MOD p] := by
      rw [heq,pow_succ]
      exact (frobenius_iter hp a).mul_right 2
    have five : p ∣ 5 := Nat.modEq_zero_iff_dvd.mp ((mod.add_right 1).symm.trans (Nat.modEq_zero_iff_dvd.mpr div))
    have hp5 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp five
    subst p
    have a2 : 2 ≤ a := by by_contra! hh; interval_cases a <;> simp_all
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le' a2
    rw [heq,Nat.add_sub_cancel,pow_add] at h25
    exact h25 ⟨5^b,by ring⟩

/-- Outside the residue class of the iterates every surviving core must fail a divisibility test. -/
def H1 : Prop := ∀ k : ℕ, 6 < k → k % 4 = 2 → k % 60 ≠ 6 →
  ¬18 ∣ k → ¬25 ∣ k-1 →
  (∀ p a : ℕ, p.Prime → k ≠ 2*p^a) → (∀ p a : ℕ, p.Prime → k ≠ p^a+1) →
  k ∣ 2^k+2 → ¬k-1 ∣ 2^k+1

/-- In the orbit's residue class the remaining issue is to show that k−2 is a power of two. -/
def H2 : Prop := ∀ k : ℕ, 6 < k → k % 60 = 6 →
  ¬18 ∣ k → ¬25 ∣ k-1 →
  (∀ p a : ℕ, p.Prime → k ≠ 2*p^a) → (∀ p a : ℕ, p.Prime → k ≠ p^a+1) →
  k ∣ 2^k+2 → k-1 ∣ 2^k+1 → ∃ s : ℕ, k=2^s+2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219037.main := by
  intro h1 h2
  let f (k : ℕ) := 2^k+2
  let seq (i : ℕ) := f^[i] 2
  have step (i : ℕ) : seq (i+1) = f (seq i) := Function.iterate_succ_apply' f i 2
  have grow (k : ℕ) : k < f k := by dsimp [f]; have := k.lt_two_pow_self; omega
  have mono : StrictMono seq := strictMono_nat_of_lt_succ (fun i => (step i) ▸ grow (seq i))
  have terms (i : ℕ) : IsTerm (seq i) := by
    induction i with
    | zero => change 2 ∣ 2^2+2 ∧ 2-1 ∣ 2^2+1; decide
    | succ i ih => rw [step]; exact term_forward ih
  have inf : (Set.ofPred IsTerm).Infinite :=
    (Set.infinite_range_of_injective mono.injective).mono (by rintro _ ⟨i,rfl⟩; exact terms i)
  have allterms (k : ℕ) (hk : IsTerm k) : k ∈ Set.range seq := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases small : k ≤ 6
      · have cases : k = 2 ∨ k = 6 := by
          have shape := term_shape hk
          omega
        rcases cases with rfl | rfl
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
      obtain ⟨_,four⟩ := term_shape hk
      obtain ⟨e,d⟩ := small_obstructions hk
      obtain ⟨ap,bp⟩ := neither_prime_power hk (by omega)
      have residue : k%60=6 := by
        by_contra hr
        exact h1 k (by omega) four hr e d ap bp hk.1 hk.2
      obtain ⟨s,hs⟩ := h2 k (by omega) residue e d ap bp hk.1 hk.2
      have s2 : 2 ≤ s := by by_contra! hlow; interval_cases s <;> simp_all
      obtain ⟨i,hi⟩ := ih s (hs ▸ grow s) (term_backward s2 (hs ▸ hk))
      exact ⟨i+1, by rw [step,hi]; exact hs.symm⟩
  have exactSeq (n : ℕ) : seq n = Nat.nth IsTerm n := by
    apply Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn seq
    · intro k hk
      obtain ⟨i,hi⟩ := allterms k hk
      exact ⟨i,fun hf => (inf hf).elim,hi⟩
    · intro i _; exact terms i
    · exact mono.strictMonoOn _
    · exact fun hf => (inf hf).elim
  intro n
  rw [←exactSeq,←exactSeq,step]

end OMA.R_oeis_a219037_R1
