import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R2
import Mathlib

/-! A collision requires at least three distinct odd prime divisors of the successor.
The argument uses the square coordinates from Vieta descent and the prime support
of the odd cofactors of the component sums. -/

open Arxiv.«1601.03081»

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R2_H2_R1

-- The Vieta step follows Abrate, Barbero, Cerruti and Murru, Theorem 4, and adapts
-- Steven Enamakel and Medulla's CrystalVieta.quotient_residues in the merged R1 branch.
private theorem square_coordinates (q : ℕ) :
    ∀ x y : ℕ, 0 < x → x ≤ y → (x+y-1)^2 = q*x*y →
      ∃ r t : ℕ, 0 < r ∧ 0 < t ∧
        ((x = r^2 ∧ y = q*t^2) ∨ (y = r^2 ∧ x = q*t^2)) := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro y hx hxy h
    by_cases hx1 : x = 1
    · subst x
      have hy : 0 < y := by omega
      have e : y*y = q*y := by simpa [pow_two] using h
      have hyq := Nat.eq_of_mul_eq_mul_right hy e
      exact ⟨1, 1, by decide, by decide, Or.inl ⟨by simp, by simpa using hyq⟩⟩
    · let z : ℤ := ((q : ℤ)-2)*x+2-y
      have hx2 : (2 : ℤ) ≤ x := by exact_mod_cast (show 2 ≤ x by omega)
      have hy : (0 : ℤ) < y := by exact_mod_cast (show 0 < y by omega)
      have hxy' : (x : ℤ) ≤ y := by exact_mod_cast hxy
      have hfix : ((x : ℤ)+y-1)^2 = (q : ℤ)*x*y := by
        have hc := congrArg (fun n : ℕ => (n : ℤ)) h
        simpa only [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ x+y), Nat.cast_add,
          Nat.cast_one, Nat.cast_mul] using hc
      have hp : (y : ℤ)*z = ((x : ℤ)-1)^2 := by dsimp [z]; nlinarith only [hfix]
      have hz : 0 < z := by
        by_contra! hz
        have hnon := mul_nonpos_of_nonneg_of_nonpos hy.le hz
        nlinarith only [hp, hnon, show (0 : ℤ) < ((x : ℤ)-1)^2 by
          exact sq_pos_of_pos (by omega)]
      have hzx : z < x := by
        by_contra! hz'
        have hm := mul_le_mul_of_nonneg_right hxy' (show (0 : ℤ) ≤ (x : ℤ) by omega)
        have hn := mul_le_mul_of_nonneg_right hz' hy.le
        nlinarith only [hp, hm, hn, hx2]
      have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz.le
      have hzN : 0 < z.toNat := by omega
      have hzxN : z.toNat < x := by omega
      have hnew : (z+(x : ℤ)-1)^2 = (q : ℤ)*z*x := by dsimp [z]; nlinarith only [hfix]
      have hnewN : (z.toNat+x-1)^2 = q*z.toNat*x := by
        rw [← Nat.cast_inj (R := ℤ)]
        simpa only [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ z.toNat+x),
          Nat.cast_add, Nat.cast_one, Nat.cast_mul, hzcast] using hnew
      obtain ⟨r,t,hr,ht,hcases⟩ := ih z.toNat hzxN x hzN hzxN.le hnewN
      have hpx : y*z.toNat = (x-1)^2 := by
        rw [← Nat.cast_inj (R := ℤ)]
        simpa only [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ x),
          Nat.cast_one, Nat.cast_mul, hzcast] using hp
      rcases hcases with ⟨hzr,hxt⟩ | ⟨hxr,hzt⟩
      · have hrd : r^2 ∣ (x-1)^2 := ⟨y, by simpa only [hzr, mul_comm] using hpx.symm⟩
        obtain ⟨w,hw⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hrd
        have hcancel : r^2*y = r^2*w^2 := by
          calc
            _ = (x-1)^2 := by simpa only [hzr,mul_comm] using hpx
            _ = _ := by rw [hw]; ring
        have hyw : y = w^2 := Nat.eq_of_mul_eq_mul_left (pow_pos hr _) hcancel
        exact ⟨w,t,by by_contra! hh; simp [show w = 0 by omega] at hyw; omega,
          ht, Or.inr ⟨hyw,hxt⟩⟩
      · have hsumSq : (z.toNat+x-1)^2 = (q*r*t)^2 := by
          rw [hnewN,hxr,hzt]
          ring
        have hsum : z.toNat+x-1 = q*r*t :=
          Nat.pow_left_injective (by decide : 2 ≠ 0) hsumSq
        have hdiff : x-1 = q*t*(r-t) := by
          have hexp : x-1 + q*t*t = q*t*r := by
            have he : z.toNat+x-1 = x-1+z.toNat := by omega
            rw [he,hzt] at hsum
            simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using hsum
          have hle : q*t*t ≤ q*t*r := by omega
          rw [Nat.mul_sub_left_distrib]
          omega
        have hqc : 0 < q*t^2 := by rw [← hzt]; exact hzN
        have hcancel : (q*t^2)*y = (q*t^2)*(q*(r-t)^2) := by
          calc
            _ = (x-1)^2 := by simpa only [hzt,mul_comm] using hpx
            _ = _ := by rw [hdiff]; ring
        have hyw : y = q*(r-t)^2 := Nat.eq_of_mul_eq_mul_left hqc hcancel
        exact ⟨r,r-t,hr,by by_contra! hh; simp [show r-t = 0 by omega] at hyw; omega,
          Or.inl ⟨hxr,hyw⟩⟩

private theorem crystal_coordinates {n a b : ℕ} (hc : IsCrystalWithComponents n a b) :
    ∃ q r t m : ℕ, 1 < r ∧ 0 < t ∧ 3 ≤ m ∧ Odd m ∧
      r^2+q*t^2 = q*r*t+1 ∧ m+1 = 2*r*t ∧
      n+1 = q*m*(m+1) ∧ n+1 = (a+b)*m := by
  obtain ⟨ho,ha,hb,hn,q,hq⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n a b).mp hc
  have habo : Odd (a*b) := hn ▸ ho
  obtain ⟨x,hx⟩ := Nat.Odd.of_mul_left habo
  obtain ⟨y,hy⟩ := Nat.Odd.of_mul_right habo
  have x0 : 0 < x := by omega
  have y0 : 0 < y := by omega
  have hnorm : (x+y+1)^2 = q*(x+1)*(y+1) := by
    have he : 4*(x+y+1)^2 = 4*(q*(x+1)*(y+1)) := by
      rw [hx,hy] at hq
      convert hq using 1 <;> ring
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) he
  have hshape : ∃ r t : ℕ, 0 < r ∧ 0 < t ∧
      ((x+1 = r^2 ∧ y+1 = q*t^2) ∨ (y+1 = r^2 ∧ x+1 = q*t^2)) := by
    rcases le_total x y with hxy | hyx
    · exact square_coordinates q (x+1) (y+1) (by omega) (by omega)
        (by convert hnorm using 2; omega)
    · obtain ⟨r,t,hr,ht,h⟩ := square_coordinates q (y+1) (x+1) (by omega) (by omega)
        (by
          have he : y+1+(x+1)-1 = x+y+1 := by omega
          rw [he,hnorm]
          ring)
      exact ⟨r,t,hr,ht,h.symm⟩
  obtain ⟨r,t,hr,ht,hshape⟩ := hshape
  have hsumCoords : r^2+q*t^2 = x+y+1+1 := by
    rcases hshape with ⟨hh,hk⟩ | ⟨hh,hk⟩
    · rw [← hh,← hk]; omega
    · rw [← hh,← hk]; omega
  have hprodCoords : (x+1)*(y+1) = r^2*(q*t^2) := by
    rcases hshape with ⟨hh,hk⟩ | ⟨hh,hk⟩
    · rw [hh,hk]
    · rw [hh,hk,mul_comm]
  have hr1 : 1 < r := by
    by_contra! h
    have he : r = 1 := by omega
    rcases hshape with ⟨hh,_⟩ | ⟨hh,_⟩ <;> simp [he] at hh <;> omega
  have hprodSum : x+y+1 = q*r*t := by
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    change (x+y+1)^2 = (q*r*t)^2
    rw [hnorm,mul_assoc q,hprodCoords]
    ring
  have hrt : 2 ≤ r*t := by simpa using Nat.mul_le_mul (show 2 ≤ r by omega) (show 1 ≤ t by omega)
  let m := 2*r*t-1
  have hm : m+1 = 2*r*t := by
    rw [show 2*r*t=2*(r*t) by ring]
    dsimp [m]
    rw [show 2*r*t=2*(r*t) by ring]
    omega
  have hm3 : 3 ≤ m := by
    rw [show 2*r*t=2*(r*t) by ring] at hm
    omega
  have hmo : Odd m := by
    refine ⟨r*t-1, ?_⟩
    rw [show 2*r*t=2*(r*t) by ring] at hm
    omega
  have hsum : a+b = q*(m+1) := by
    rw [hx,hy,hm]
    calc
      _ = 2*(x+y+1) := by ring
      _ = _ := by rw [hprodSum]; ring
  have he : n+1+(a+b) = 4*(r^2*(q*t^2)) := by
    rw [hn,hx,hy,← hprodCoords]
    ring
  have hN : n+1 = q*m*(m+1) := by
    have hsq : 4*(r^2*(q*t^2)) = q*(m+1)*(m+1) := by rw [hm]; ring
    rw [hsum,hsq] at he
    nlinarith only [he]
  exact ⟨q,r,t,m,hr1,ht,hm3,hmo,hsumCoords.trans (by rw [hprodSum]),hm,hN,
    by rw [hN,hsum]; ring⟩

-- The equal-sum, equal-product argument follows Steven Enamakel and Medulla's R1 reduction.
private theorem pairs_eq_of_sum_prod {a b c d : ℕ} (hs : a+b = c+d) (hp : a*b = c*d) :
    ({a,b} : Finset ℕ) = {c,d} := by
  have hsZ : (a : ℤ)+b = (c : ℤ)+d := by exact_mod_cast hs
  have hpZ : (a : ℤ)*b = (c : ℤ)*d := by exact_mod_cast hp
  have hz : ((a : ℤ)-c)*((a : ℤ)-d) = 0 := by
    calc
      _ = (a : ℤ)^2-a*((c : ℤ)+d)+(c : ℤ)*d := by ring
      _ = 0 := by rw [← hsZ,← hpZ]; ring
  rcases mul_eq_zero.mp hz with hz | hz
  · have hac : a=c := by exact_mod_cast sub_eq_zero.mp hz
    subst c
    have hbd : b=d := by omega
    simp [hbd]
  · have had : a=d := by exact_mod_cast sub_eq_zero.mp hz
    subst d
    have hbc : b=c := by omega
    simp [hbc, Finset.pair_comm]

private theorem square_sub_one {r : ℕ} (hr : 1 ≤ r) : (r-1)*(r+1) = r^2-1 := by
  have hrsq : 1 ≤ r^2 := by simpa using Nat.pow_le_pow_left hr 2
  rw [← Nat.cast_inj (R := ℤ)]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hr, Nat.cast_sub hrsq,
    Nat.cast_pow, Nat.cast_one]
  ring

private theorem coordinate_arithmetic {q r t : ℕ} (hr : 1 < r) (ht : 0 < t)
    (h : r^2+q*t^2 = q*r*t+1) :
    t < r ∧ 3 ≤ q ∧ q ≤ r+1 ∧ q*t ∣ r^2-1 := by
  have hZ : (r : ℤ)^2+(q : ℤ)*(t : ℤ)^2 = (q : ℤ)*r*t+1 := by exact_mod_cast h
  have hrZ : (1 : ℤ) < r := by exact_mod_cast hr
  have hqZ : (0 : ℤ) ≤ q := by positivity
  have htZ : (0 : ℤ) < t := by exact_mod_cast ht
  have htr : t < r := by
    by_contra! hn
    have hnZ : (0 : ℤ) ≤ (t : ℤ)-r := by
      have : (r : ℤ) ≤ t := by exact_mod_cast hn
      omega
    nlinarith only [hZ, mul_nonneg (mul_nonneg hqZ htZ.le) hnZ,
      mul_pos (by omega : (0 : ℤ) < (r : ℤ)-1) (by omega : (0 : ℤ) < (r : ℤ)+1)]
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_lt htr
  have he : r^2-1 = (q*t)*(k+1) := by
    have hmul : q*r*t = q*t^2 + q*t*(k+1) := by rw [hk]; ring
    omega
  have htk : r-1 ≤ t*(k+1) := by
    have heq : r=t+k+1 := by omega
    rw [heq]
    simp only [Nat.add_sub_cancel]
    nlinarith only [Nat.le_mul_of_pos_left (m := k) ht]
  have hup : q ≤ r+1 := by
    have hl := Nat.mul_le_mul_left q htk
    apply Nat.le_of_mul_le_mul_right
    · calc
        q*(r-1) ≤ q*(t*(k+1)) := hl
        _ = r^2-1 := by rw [he]; ring
        _ = (r+1)*(r-1) := by rw [mul_comm, square_sub_one (by omega : 1 ≤ r)]
    · omega
  have hlow : 3 ≤ q := by
    by_contra! hlt
    have hp : (1 : ℤ) ≤ (t : ℤ)*((k : ℤ)+1) := by
      have hpos : 0 < t*(k+1) := Nat.mul_pos ht (by omega)
      exact_mod_cast (show 1 ≤ t*(k+1) by omega)
    have hq2 : (q : ℤ) ≤ 2 := by exact_mod_cast (show q ≤ 2 by omega)
    have heq : (r : ℤ) = (t : ℤ)+k+1 := by exact_mod_cast (show r=t+k+1 by omega)
    have h1 : (r : ℤ)^2-1 = (q : ℤ)*t*((k : ℤ)+1) := by
      nlinarith only [hZ, congrArg (fun x : ℤ => (q : ℤ)*t*x) heq]
    have h2 : (r : ℤ)^2 = ((t : ℤ)+k+1)^2 := by rw [heq]
    nlinarith only [h1,h2,hp,sq_nonneg ((t : ℤ)-(k+1)),
      mul_le_mul_of_nonneg_right hq2 (show (0 : ℤ) ≤ (t : ℤ)*((k : ℤ)+1) by positivity)]
  exact ⟨htr,hlow,hup,⟨k+1,he⟩⟩

private theorem prime_power_le {p e r t q m : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hr : 1 < r) (ht : 0 < t) (hm : m+1 = 2*r*t)
    (h : r^2+q*t^2 = q*r*t+1) (hpm : ¬ p ∣ m)
    (hd : p^e ∣ q*m*(m+1)) : p^e ≤ r+1 := by
  have h2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (fun h =>
    hpo.not_two_dvd_nat (by rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h]))
  have hcm : (p^e).Coprime m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left _
  have hdiv : p^e ∣ r*(q*t) := by
    apply (h2.pow_left e).dvd_mul_left.mp
    apply hcm.dvd_mul_left.mp
    simpa only [hm,mul_assoc,mul_comm,mul_left_comm] using hd
  have hdvd := (coordinate_arithmetic hr ht h).2.2.2
  have hpNr : ¬ p ∣ r ∨ ¬ p ∣ q*t := by
    by_contra! hboth
    have hps : p ∣ r^2 := hboth.1.trans (dvd_pow_self _ (by decide))
    have hpd := hboth.2.trans hdvd
    have hh : 1+(r^2-1)=r^2 := by
      have : 1 ≤ r^2 := by simpa using Nat.pow_le_pow_left (show 1 ≤ r by omega) 2
      omega
    have hh' : p ∣ 1 := (Nat.dvd_add_iff_left hpd).mpr (by rw [hh]; exact hps)
    exact hp.not_dvd_one hh'
  rcases hpNr with hnr | hnqt
  · have hdiv' := ((hp.coprime_iff_not_dvd.mpr hnr).pow_left e).dvd_mul_left.mp hdiv
    have hr' : p^e ∣ (r-1)*(r+1) := by
      rw [square_sub_one (by omega : 1 ≤ r)]
      exact hdiv'.trans hdvd
    have hpSplit : ¬ p ∣ r-1 ∨ ¬ p ∣ r+1 := by
      by_contra! hboth
      have id : 2+(r-1)=r+1 := by omega
      have hpd : p ∣ 2 := (Nat.dvd_add_iff_left hboth.1).mpr (by rw [id]; exact hboth.2)
      exact (hp.coprime_iff_not_dvd.mp h2) hpd
    have hle : p^e ≤ r+1 := by
      rcases hpSplit with hl | hl
      · exact Nat.le_of_dvd (by omega) (((hp.coprime_iff_not_dvd.mpr hl).pow_left e).dvd_mul_left.mp hr')
      · exact (Nat.le_of_dvd (by omega) (((hp.coprime_iff_not_dvd.mpr hl).pow_left e).dvd_mul_right.mp hr')).trans (by omega)
    exact hle
  · have hdiv' := ((hp.coprime_iff_not_dvd.mpr hnqt).pow_left e).dvd_mul_right.mp hdiv
    exact (Nat.le_of_dvd (by omega : 0 < r) hdiv').trans (by omega)

private theorem cofactor_not_dvd {m k A B : ℕ} (hm : 3 ≤ m) (hmk : m < k)
    (hA : 0 < A) (hAb : 2*A ≤ m+3)
    (h : A*m*(m+1) = B*k*(k+1)) : ¬ m ∣ k := by
  rintro ⟨j, hj⟩
  have hj2 : 2 ≤ j := by
    by_contra! hj2
    interval_cases j <;> simp_all
  have he : A*(m+1) = (k+1)*(B*j) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < m)
    calc
      m*(A*(m+1)) = A*m*(m+1) := by ring
      _ = B*k*(k+1) := h
      _ = _ := by rw [hj]; ring
  have hd : k+1 ∣ (j-1)*A := by
    have hmul : k+1 ∣ A*(m+1)*j := by rw [he]; exact (dvd_mul_right (k+1) (B*j)).mul_right j
    have hid : A*(m+1)*j = (j-1)*A + (k+1)*A := by
      have hsub : j-1+1 = j := by omega
      nlinarith only [congrArg (fun v : ℕ => v*A) hsub,
        congrArg (fun v : ℕ => v*A) hj]
    rw [hid] at hmul
    exact (Nat.dvd_add_iff_left (dvd_mul_right _ _)).mpr hmul
  have hsmall : (j-1)*A < k+1 := calc
    (j-1)*A ≤ j*m := Nat.mul_le_mul (by omega) (by omega)
    _ < k+1 := by rw [hj, Nat.mul_comm j m]; omega
  exact (Nat.not_dvd_of_pos_of_lt (mul_pos (by omega) hA) hsmall) hd

private theorem two_pow_add_one_eq_three_pow {e f : ℕ}
    (he : 0 < e) (h : 2^e+1 = 3^f) : 2^e = 2 ∨ 2^e = 8 := by
  by_cases he1 : e = 1
  · left
    simp [he1]
  right
  have he2 : 2 ≤ e := by omega
  have h4 : 4 ∣ 2^e := by
    convert Nat.pow_dvd_pow 2 he2 using 1
  have hf : Even f := by
    by_contra hf
    obtain ⟨i,hi⟩ := Nat.not_even_iff_odd.mp hf
    have hbase : (3 : ℕ) ≡ 3 [MOD 4] := Nat.ModEq.refl _
    have hsq : (9 : ℕ) ≡ 1 [MOD 4] := by decide
    have hmod : (3 : ℕ)^f ≡ 3 [MOD 4] := by
      rw [hi,pow_succ,pow_mul]
      simpa using (hsq.pow i).mul hbase
    have hone : (2 : ℕ)^e+1 ≡ 1 [MOD 4] := by
      rw [Nat.ModEq, Nat.add_mod, Nat.mod_eq_zero_of_dvd h4]
    rw [h] at hone
    have hf' : (3 : ℕ) ≡ 1 [MOD 4] := hmod.symm.trans hone
    exact (by decide : ¬ (3 : ℕ) ≡ 1 [MOD 4]) hf'
  obtain ⟨i,hi⟩ := hf
  let w := 3^i
  have hw3 : 3 ≤ w := by
    by_cases hi0 : i = 0
    · simp [hi,hi0] at h
    · dsimp [w]
      simpa using Nat.pow_le_pow_right (by decide : 0 < 3) (show 1 ≤ i by omega)
  have hfactor : (w-1)*(w+1) = 2^e := by
    have hZ : (2 : ℤ)^e+1 = (3 : ℤ)^f := by exact_mod_cast h
    rw [hi,← mul_two,pow_mul] at hZ
    have hwZ : (w : ℤ) = (3 : ℤ)^i := by simp [w]
    rw [← Nat.cast_inj (R := ℤ)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ w)]
    rw [hwZ]
    nlinarith only [hZ]
  have hwp : w = 3 := by
    by_contra! hne
    have hw5 : 4 ≤ w := by omega
    obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show w-1 ∣ 2^e from ⟨w+1,hfactor.symm⟩)
    obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show w+1 ∣ 2^e from ⟨w-1,by simpa [mul_comm] using hfactor.symm⟩)
    have hj2 : 2 ≤ j := by
      by_contra! hlt
      interval_cases j <;> norm_num at hj <;> omega
    have hk2 : 2 ≤ k := by
      by_contra! hlt
      interval_cases k <;> norm_num at hk <;> omega
    have hleft : 4 ∣ w-1 := by rw [hj]; exact Nat.pow_dvd_pow 2 hj2
    have hright : 4 ∣ w+1 := by rw [hk]; exact Nat.pow_dvd_pow 2 hk2
    have hid : 2+(w-1)=w+1 := by omega
    exact (by decide : ¬ 4 ∣ 2) ((Nat.dvd_add_iff_left hleft).mpr (hid ▸ hright))
  simpa [hwp] using hfactor.symm

private theorem full_odd_support {N q r t m : ℕ} (hr : 1 < r)
    (hcoord : r^2+q*t^2 = q*r*t+1) (hm : m+1=2*r*t) (hN : N=q*m*(m+1))
    (hs : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ N → p ∣ m) :
    N = 36 ∨ N = 2160 := by
  have hcop : m.Coprime (m+1) := by simp
  have hmN : m+1 ∣ N := by rw [hN]; exact dvd_mul_left _ _
  have hsupport {p v : ℕ} (hp : p.Prime) (hpv : p ∣ v) (hvm : v ∣ m+1) : p=2 := by
    by_contra hne
    have hpm := hs p hp hne (hpv.trans (hvm.trans hmN))
    exact hp.not_dvd_one (by
      have hg : p ∣ m.gcd (m+1) := Nat.dvd_gcd hpm (hpv.trans hvm)
      rwa [hcop.gcd_eq_one] at hg)
  have hrm : r ∣ m+1 := by rw [hm]; exact ⟨2*t,by ring⟩
  have htm : t ∣ m+1 := by rw [hm]; exact dvd_mul_left _ _
  obtain ⟨p,hp,hpr⟩ := Nat.exists_prime_and_dvd (show r ≠ 1 by omega)
  have h2r : 2 ∣ r := by rwa [hsupport hp hpr hrm] at hpr
  have ht1 : t=1 := by
    by_contra ht1
    obtain ⟨p,hp,hpt⟩ := Nat.exists_prime_and_dvd ht1
    have h2t : 2 ∣ t := by rwa [hsupport hp hpt htm] at hpt
    have hl : 2 ∣ r^2+q*t^2 :=
      dvd_add (h2r.trans (dvd_pow_self _ (by decide))) ((h2t.trans (dvd_pow_self _ (by decide))).mul_left q)
    rw [hcoord] at hl
    exact (by decide : ¬ 2 ∣ 1) ((Nat.dvd_add_iff_right ((h2t.mul_left (q*r)))).mpr hl)
  have hq : q=r+1 := by
    have hZ : (r : ℤ)^2+(q : ℤ)= (q : ℤ)*r+1 := by
      exact_mod_cast (by simpa [ht1] using hcoord : r^2+q=q*r+1)
    have hmul : ((r : ℤ)-1)*((q : ℤ)-r-1)=0 := by nlinarith only [hZ]
    rcases mul_eq_zero.mp hmul with h | h <;> omega
  have hqOdd : Odd q := by
    obtain ⟨j,hj⟩ := h2r
    exact ⟨j, by omega⟩
  have hqpow : q = 3^q.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd (by omega : q ≠ 0)
    intro p hp hpq
    have hp2 : p ≠ 2 := fun h => hqOdd.not_two_dvd_nat (h ▸ hpq)
    have hpN : p ∣ N := by rw [hN]; exact (hpq.mul_right m).mul_right (m+1)
    have hpm := hs p hp hp2 hpN
    have hid : 3+m=2*q := by
      rw [ht1, mul_one] at hm
      omega
    have hp3 : p ∣ 3 := (Nat.dvd_add_iff_left hpm).mpr (hid ▸ hpq.mul_left 2)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
  have hrpow : r = 2^r.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega : r ≠ 0)
      (fun hp hpr => hsupport hp hpr hrm)
  have he : 0 < r.primeFactorsList.length := by
    by_contra! he
    have hh : r.primeFactorsList.length=0 := by omega
    simp [hh] at hrpow
    omega
  have hpow : 2^r.primeFactorsList.length+1 = 3^q.primeFactorsList.length := by
    rw [← hrpow,← hqpow,hq]
  rcases two_pow_add_one_eq_three_pow he hpow with hh | hh
  · have hr2 : r=2 := hrpow.trans hh
    have hq3 : q=3 := by omega
    have hm3 : m=3 := by simp [ht1,hr2] at hm; omega
    left
    norm_num [hN,hq3,hm3]
  · have hr8 : r=8 := hrpow.trans hh
    have hq9 : q=9 := by omega
    have hm15 : m=15 := by simp [ht1,hr8] at hm; omega
    right
    norm_num [hN,hq9,hm15]

private theorem prime_product_pair {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 1 < a) (hb : 1 < b) (h : p*q=a*b) :
    ({a,b} : Finset ℕ) = {p,q} := by
  have aux {x y : ℕ} (hy : 1 < y) (hm : p*q=x*y) (hd : p ∣ x) :
      ({x,y} : Finset ℕ) = {p,q} := by
    obtain ⟨j,rfl⟩ := hd
    have he : q = j*y := Nat.eq_of_mul_eq_mul_left hp.pos (by simpa [mul_assoc] using hm)
    rcases (Nat.dvd_prime hq).mp (show j ∣ q from ⟨y,he⟩) with hj | hj
    · simp [hj] at he
      simp [hj,he]
    · have hy1 : y=1 := Nat.eq_of_mul_eq_mul_left hq.pos (by simpa [hj] using he.symm)
      omega
  have hd : p ∣ a*b := by rw [← h]; exact dvd_mul_right _ _
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact aux hb h hd
  · rw [Finset.pair_comm a b]
    exact aux ha (by simpa [mul_comm b a] using h) hd

private theorem missing_prime {N q r t m : ℕ} (hr : 1 < r)
    (hcoord : r^2+q*t^2=q*r*t+1) (hm : m+1=2*r*t) (hN : N=q*m*(m+1))
    (h36 : N ≠ 36) (h2160 : N ≠ 2160) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ N ∧ ¬ p ∣ m := by
  by_contra! h
  exact (full_odd_support hr hcoord hm hN h).elim h36 h2160

private theorem ordered_cofactor_cases
    {N q r t m Q R T k : ℕ}
    (hr : 1 < r) (ht : 0 < t) (hR : 1 < R)
    (hc : r^2+q*t^2=q*r*t+1) (hC : R^2+Q*T^2=Q*R*T+1)
    (hm : m+1=2*r*t) (hk : k+1=2*R*T) (hm3 : 3 ≤ m) (hmk : m < k)
    (hN : N=q*m*(m+1)) (hN' : N=Q*k*(k+1))
    (h36 : N ≠ 36) (h2160 : N ≠ 2160) :
    (¬ m ∣ k ∧
      (∀ p e : ℕ, p.Prime → p^e ∣ k → ¬ p ∣ m → p^e ≤ r+1) ∧
      (∃ p l s : ℕ, p.Prime ∧ l.Prime ∧ s.Prime ∧ p ≠ l ∧
        p ∣ k ∧ l ∣ k ∧ s ≠ 2 ∧ s ∣ N ∧ ¬ s ∣ k)) ∨
    (∃ p e l s : ℕ, p.Prime ∧ k = p^e ∧ p ∣ m ∧
      l.Prime ∧ l ≠ p ∧ l ∣ m ∧ s.Prime ∧ s ≠ 2 ∧ s ∣ N ∧ ¬ s ∣ m) := by
  obtain ⟨p,hp,hpk⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  have hko : Odd k := by
    refine ⟨R*T-1,?_⟩
    rw [show 2*R*T=2*(R*T) by ring] at hk
    omega
  have hkN : k ∣ N := by rw [hN']; exact (dvd_mul_left k Q).mul_right (k+1)
  have hbound (l e : ℕ) (hl : l.Prime) (hlk : l^e ∣ k) (hlm : ¬ l ∣ m) : l^e ≤ r+1 := by
    by_cases he : e = 0
    · simp [he]
    have hld : l ∣ k := (dvd_pow_self l he).trans hlk
    have hlo : Odd l := hl.odd_of_ne_two (fun h => hko.not_two_dvd_nat (h ▸ hld))
    rw [hN] at hkN
    exact prime_power_le hl hlo hr ht hm hc hlm (hlk.trans hkN)
  have hnot : ¬ m ∣ k := by
    have hcoord := coordinate_arithmetic hr ht hc
    have hmr : 2*r ≤ 2*r*t := by
      simpa using Nat.mul_le_mul_left (2*r) (show 1 ≤ t by omega)
    exact cofactor_not_dvd hm3 hmk (by have := hcoord.2.1; omega)
      (by have := hcoord.2.2.1; omega) (hN.symm.trans hN')
  by_cases hmore : ∃ l : ℕ, l.Prime ∧ l ≠ p ∧ l ∣ k
  · obtain ⟨l,hl,hlp,hlk⟩ := hmore
    obtain ⟨s,hs,hs2,hsN,hsk⟩ := missing_prime hR hC hk hN' h36 h2160
    exact Or.inl ⟨hnot,hbound,p,l,s,hp,hl,hs,hlp.symm,hpk,hlk,hs2,hsN,hsk⟩
  · let e := k.primeFactorsList.length
    have hpow : k=p^e := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd (by omega : k ≠ 0)
      intro l hl hlk
      by_contra hlp
      exact hmore ⟨l,hl,hlp,hlk⟩
    have hpm : p ∣ m := by
      by_contra! hpm
      have hle := hbound p e hp (by rw [hpow]) hpm
      have hmr : 2*r ≤ 2*r*t := by
        simpa using Nat.mul_le_mul_left (2*r) (show 1 ≤ t by omega)
      omega
    have hmore' : ∃ l : ℕ, l.Prime ∧ l ≠ p ∧ l ∣ m := by
      by_contra hh
      have hmPow : m=p^m.primeFactorsList.length := by
        apply Nat.eq_prime_pow_of_unique_prime_dvd (by omega : m ≠ 0)
        intro l hl hlm
        by_contra hlp
        exact hh ⟨l,hl,hlp,hlm⟩
      have hle : m.primeFactorsList.length ≤ e := by
        by_contra! hlt
        have hge := Nat.pow_le_pow_right hp.pos hlt.le
        rw [← hmPow,← hpow] at hge
        omega
      have hd : m ∣ k := by rw [hmPow,hpow]; exact Nat.pow_dvd_pow p hle
      exact hnot hd
    obtain ⟨l,hl,hlp,hlm⟩ := hmore'
    obtain ⟨s,hs,hs2,hsN,hsm⟩ := missing_prime hr hc hm hN h36 h2160
    exact Or.inr ⟨p,e,l,s,hp,hpow,hpm,hl,hlp,hlm,hs,hs2,hsN,hsm⟩

private theorem collision_data {n a b c d : ℕ}
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d)
    (hne : ({a,b} : Finset ℕ) ≠ {c,d}) :
    ∃ q r t m Q R T k : ℕ,
      1 < r ∧ 0 < t ∧ 1 < R ∧ 0 < T ∧
      r^2+q*t^2 = q*r*t+1 ∧ R^2+Q*T^2 = Q*R*T+1 ∧
      m+1 = 2*r*t ∧ k+1 = 2*R*T ∧ 3 ≤ m ∧ m < k ∧
      n+1 = q*m*(m+1) ∧ n+1 = Q*k*(k+1) ∧
      ((¬ m ∣ k ∧
        (∀ p e : ℕ, p.Prime → p^e ∣ k → ¬ p ∣ m → p^e ≤ r+1) ∧
        (∃ p l s : ℕ, p.Prime ∧ l.Prime ∧ s.Prime ∧ p ≠ l ∧
          p ∣ k ∧ l ∣ k ∧ s ≠ 2 ∧ s ∣ n+1 ∧ ¬ s ∣ k)) ∨
       (∃ p e l s : ℕ, p.Prime ∧ k = p^e ∧ p ∣ m ∧
          l.Prime ∧ l ≠ p ∧ l ∣ m ∧ s.Prime ∧ s ≠ 2 ∧ s ∣ n+1 ∧ ¬ s ∣ m)) := by
  obtain ⟨_,ha,hb,habn,_⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n a b).mp hab
  obtain ⟨_,hc,hd,hcdn,_⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n c d).mp hcd
  have exclude_prime_product {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p*q=n) : False :=
    hne ((prime_product_pair hp hq ha hb (h.trans habn)).trans
      (prime_product_pair hp hq hc hd (h.trans hcdn)).symm)
  have h36 : n+1 ≠ 36 := fun h =>
    exclude_prime_product Nat.prime_five Nat.prime_seven (by omega)
  have h2160 : n+1 ≠ 2160 := fun h =>
    exclude_prime_product (by decide : Nat.Prime 17) (by decide : Nat.Prime 127) (by omega)
  obtain ⟨q,r,t,m,hr,ht,hm3,_,hcrt,hm,hN,hs⟩ := crystal_coordinates hab
  obtain ⟨Q,R,T,k,hR,hT,hk3,_,hCRT,hk,hN',hs'⟩ := crystal_coordinates hcd
  rcases lt_trichotomy m k with hlt | he | hgt
  · exact ⟨q,r,t,m,Q,R,T,k,hr,ht,hR,hT,hcrt,hCRT,hm,hk,hm3,hlt,hN,hN',
      ordered_cofactor_cases hr ht hR hcrt hCRT hm hk hm3 hlt hN hN' h36 h2160⟩
  · subst k
    exact (hne (pairs_eq_of_sum_prod
      (Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) (hs.symm.trans hs'))
      (habn.symm.trans hcdn))).elim
  · exact ⟨Q,R,T,k,q,r,t,m,hR,hT,hr,ht,hCRT,hcrt,hk,hm,hk3,hgt,hN',hN,
      ordered_cofactor_cases hR hT hr hCRT hcrt hk hm hk3 hgt hN' hN h36 h2160⟩

/-- Two different crystal pairs require three distinct odd primes dividing the successor. -/
theorem three_odd_primes_of_collision {n a b c d : ℕ}
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d)
    (hne : ({a,b} : Finset ℕ) ≠ {c,d}) :
    ∃ p l s : ℕ, p.Prime ∧ l.Prime ∧ s.Prime ∧ Odd p ∧ Odd l ∧ Odd s ∧
      p ≠ l ∧ p ≠ s ∧ l ≠ s ∧ p ∣ n+1 ∧ l ∣ n+1 ∧ s ∣ n+1 := by
  obtain ⟨q,r,t,m,Q,R,T,k,_,_,_,_,_,_,hm,hk,hm3,hmk,hN,hN',hcase⟩ :=
    collision_data hab hcd hne
  have odd_cofactor {v x y : ℕ} (h : v+1=2*x*y) : Odd v := by
    refine ⟨x*y-1,?_⟩
    rw [show 2*x*y=2*(x*y) by ring] at h
    omega
  have collect {v p l s : ℕ} (hvo : Odd v) (hvN : v ∣ n+1)
      (hp : p.Prime) (hl : l.Prime) (hs : s.Prime) (hpl : p ≠ l)
      (hpv : p ∣ v) (hlv : l ∣ v) (hs2 : s ≠ 2) (hsN : s ∣ n+1) (hsv : ¬ s ∣ v) :
      ∃ p l s : ℕ, p.Prime ∧ l.Prime ∧ s.Prime ∧ Odd p ∧ Odd l ∧ Odd s ∧
        p ≠ l ∧ p ≠ s ∧ l ≠ s ∧ p ∣ n+1 ∧ l ∣ n+1 ∧ s ∣ n+1 := by
    refine ⟨p,l,s,hp,hl,hs,?_,?_,hs.odd_of_ne_two hs2,hpl,?_,?_,hpv.trans hvN,hlv.trans hvN,hsN⟩
    · exact hp.odd_of_ne_two (fun h => hvo.not_two_dvd_nat (h ▸ hpv))
    · exact hl.odd_of_ne_two (fun h => hvo.not_two_dvd_nat (h ▸ hlv))
    · exact fun h => hsv (h ▸ hpv)
    · exact fun h => hsv (h ▸ hlv)
  rcases hcase with ⟨_,_,p,l,s,hp,hl,hs,hpl,hpk,hlk,hs2,hsN,hsk⟩ |
    ⟨p,_,l,s,hp,_,hpm,hl,hlp,hlm,hs,hs2,hsN,hsm⟩
  · exact collect (odd_cofactor hk) (by rw [hN']; exact (dvd_mul_left k Q).mul_right _) hp hl hs
      hpl hpk hlk hs2 hsN hsk
  · exact collect (odd_cofactor hm) (by rw [hN]; exact (dvd_mul_left m q).mul_right _) hp hl hs
      hlp.symm hpm hlm hs2 hsN hsm

/-- The larger cofactor has two distinct prime divisors, and misses an odd prime of the successor. -/
def H1 : Prop :=
  ∀ N q r t m Q R T k : ℕ,
    1 < r → 0 < t → 1 < R → 0 < T →
    r^2+q*t^2 = q*r*t+1 → R^2+Q*T^2 = Q*R*T+1 →
    m+1 = 2*r*t → k+1 = 2*R*T → 3 ≤ m → m < k →
    N = q*m*(m+1) → N = Q*k*(k+1) →
    ¬ m ∣ k →
    (∀ p e : ℕ, p.Prime → p^e ∣ k → ¬ p ∣ m → p^e ≤ r+1) →
    (∃ p l s : ℕ, p.Prime ∧ l.Prime ∧ s.Prime ∧ p ≠ l ∧
      p ∣ k ∧ l ∣ k ∧ s ≠ 2 ∧ s ∣ N ∧ ¬ s ∣ k) →
    False

/-- The larger cofactor is a prime power, and its prime divides the smaller cofactor. -/
def H2 : Prop :=
  ∀ N q r t m Q R T k : ℕ,
    1 < r → 0 < t → 1 < R → 0 < T →
    r^2+q*t^2 = q*r*t+1 → R^2+Q*T^2 = Q*R*T+1 →
    m+1 = 2*r*t → k+1 = 2*R*T → 3 ≤ m → m < k →
    N = q*m*(m+1) → N = Q*k*(k+1) →
    (∃ p e l s : ℕ, p.Prime ∧ k = p^e ∧ p ∣ m ∧
      l.Prime ∧ l ≠ p ∧ l ∣ m ∧ s.Prime ∧ s ≠ 2 ∧ s ∣ N ∧ ¬ s ∣ m) →
    False

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R2.H2 := by
  intro h₁ h₂ n a b c d hab hcd _
  by_contra hne
  obtain ⟨q,r,t,m,Q,R,T,k,hr,ht,hR,hT,hc,hC,hm,hk,hm3,hmk,hN,hN',hcase⟩ :=
    collision_data hab hcd hne
  rcases hcase with ⟨hnot,hbound,hs⟩ | hs
  · exact h₁ (n+1) q r t m Q R T k hr ht hR hT hc hC hm hk hm3 hmk hN hN' hnot hbound hs
  · exact h₂ (n+1) q r t m Q R T k hr ht hR hT hc hC hm hk hm3 hmk hN hN' hs

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R2_H2_R1
