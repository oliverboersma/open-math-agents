import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Tactic

/-! The full-gcd case reduces to two residual cofactor branches. -/

namespace CrystalFullGcdSplit

private theorem mod_succ_zero {x y : ℕ} (hy : 1 < y)
    (hmod : (x % y + 1) % y = 0) : x % y = y-1 := by
  have hlt : x % y < y := Nat.mod_lt _ (by omega)
  have hdvd : y ∣ x % y + 1 := Nat.dvd_of_mod_eq_zero hmod
  have hle : y ≤ x % y + 1 := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem mod_predecessor_zero {x y : ℕ} (hy : 1 < y) (hx : x < y)
    (hmod : (x + (y-1)) % y = 0) : x = 1 := by
  have hdvd : y ∣ x + (y-1) := Nat.dvd_of_mod_eq_zero hmod
  rcases hdvd with ⟨t,ht⟩
  have htpos : 0 < t := by
    by_contra hn
    have ht0 : t=0 := by omega
    rw [ht0] at ht
    omega
  have htwolt : t < 2 := by
    by_contra hn
    have htwo : 2≤t := by omega
    have hmul := Nat.mul_le_mul_left y htwo
    have hsumlt : x+(y-1)<2*y := by omega
    nlinarith only [ht,hmul,hsumlt]
  have htone : t=1 := by omega
  rw [htone] at ht
  omega

private theorem first_component_bound {g y z : ℕ}
    (hg : 2 ≤ g) (ho : g*y ≤ z) (hdiv : g+y*z ∣ g*y*z+1) :
    y^2+1 < g := by
  have hmul : g+y*z ∣ g*(g+y*z) := dvd_mul_left _ _
  have hsub := Nat.dvd_sub hmul hdiv
  have hdiff : g*(g+y*z)-(g*y*z+1)=g^2-1 := by
    have heq : g*(g+y*z)=g*y*z+g^2 := by ring
    omega
  rw [hdiff] at hsub
  have hsq : 1 < g^2 := by nlinarith
  have hs : g+y*z ≤ g^2-1 := Nat.le_of_dvd (by omega) hsub
  have hs' : g+y*z < g^2 := by omega
  have hb := Nat.mul_le_mul_left y ho
  have hgY : g*(y^2+1) ≤ g+y*z := by nlinarith only [hb]
  by_contra! h
  have hmul' := Nat.mul_le_mul_left g h
  nlinarith only [hs',hgY,hmul']

private theorem scaled_bounds {g y z q k D : ℕ}
    (hg : 2 ≤ g) (hy : 2 ≤ y) (ho : g*y ≤ z)
    (hgY : y^2+1 < g) (hD : D ≤ y^2-1) (hk : 0 < k)
    (heq : k*((g+y*z)*(g*y+z))=D*(g*y*z+1))
    (hq : 0 < q) (hquot : (g*y+z)^2=q*((g*y+1)*(z+1))) :
    k*(z+g*y) < g*D ∧ k*y*q < D+2*k*y := by
  have hyp : 0 < y := by omega
  have hgp : 0 < g := by omega
  have hzp : 0 < z := lt_of_lt_of_le (Nat.mul_pos hgp hyp) ho
  have hgz : g ≤ k*(g*z) := by
    calc
      g ≤ g*z := by
        simpa using Nat.mul_le_mul_left g (show 1 ≤ z by omega)
      _ ≤ k*(g*z) := by
        simpa using Nat.mul_le_mul_right (g*z) (show 1 ≤ k by omega)
  have hsmall : D < k*(g*z) := by omega
  have hprod : k*(y*z)*(z+g*y)+k*(g*z)+k*g^2*y =
      D*(g*y*z)+D := by nlinarith only [heq]
  have hless : k*(z+g*y) < g*D := by
    by_contra! h
    have hh := Nat.mul_le_mul_left (y*z) h
    nlinarith only [hh,hprod,hsmall,Nat.zero_le (k*g^2*y)]
  refine ⟨hless, ?_⟩
  have hleft := Nat.mul_lt_mul_of_pos_left hless (Nat.mul_pos hyp hzp)
  have hright := Nat.mul_le_mul_left (k*g*y^2) (show g*y+z ≤ 2*z by omega)
  have hden : g*y*z < (g*y+1)*(z+1) := by nlinarith
  have hqgyz := Nat.mul_lt_mul_of_pos_left hden hq
  rw [← hquot] at hqgyz
  have hscaled := Nat.mul_lt_mul_of_pos_left hqgyz (Nat.mul_pos hk hyp)
  have hout : (k*y*q)*(g*y*z)<(D+2*k*y)*(g*y*z) := by
    nlinarith only [hleft,hright,hscaled]
  exact Nat.lt_of_mul_lt_mul_right hout

private theorem scaled_quotient_lower {g y z q k D r : ℕ}
    (hg : 2 ≤ g) (hy : 4 ≤ y) (hz : 0 < z) (hk : 0 < k)
    (hgY : y^2+1 < g) (hD : D ≤ y^2-1) (hscale : k*(z+g*y) < g*D)
    (hp : k*((g+y*z)*(g*y+z)) = D*(g*y*z+1))
    (hr : (g*y+z)*r = g*y*z+1)
    (hq : (g*y+z)^2 = q*((g*y+1)*(z+1))) : D+k*y < k*y*q := by
  have hsum : 0 < g*y+z := by positivity
  have hden : (g*y+1)*(z+1) = (g*y+z)*(r+1) := by
    nlinarith only [hr]
  have hq' : g*y+z = q*(r+1) := by
    apply Nat.eq_of_mul_eq_mul_left hsum
    rw [hden] at hq
    nlinarith only [hq]
  have hr' : k*(g+y*z)=D*r := by
    apply Nat.eq_of_mul_eq_mul_left hsum
    nlinarith only [hp, congrArg (D*·) hr]
  have hmatch : q*(k*(g+y*z)+D)=D*(g*y+z) := by
    rw [hr']
    nlinarith only [congrArg (D*·) hq']
  have hDy : D ≤ y^2 := by omega
  have hdkg : D ≤ k*g := by
    have hkg : g ≤ k*g := by
      simpa only [one_mul] using Nat.mul_le_mul_right g (show 1 ≤ k by omega)
    exact le_trans (by omega) hkg
  have hdksq : D ≤ k*y^2 := by
    have hyk : y^2 ≤ k*y^2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (y^2) (show 1 ≤ k by omega)
    exact hDy.trans hyk
  have hyprod := Nat.mul_le_mul_right y (show 2 ≤ y by omega)
  have hycube : 3*y^2 < y^3 := by
    have hk' := Nat.mul_lt_mul_of_pos_right (show 3 < y by omega)
      (show 0 < y^2 by positivity)
    nlinarith only [hk']
  have hsumY : 2*y^2+2*y < y^3 := by nlinarith only [hyprod,hycube]
  have hsmall : D*k*g + D^2 + k^2*y*g + k*y*D < k^2*g*y^3 := by
    have hBd := Nat.mul_le_mul_left D hdkg
    have hBy := Nat.mul_le_mul_left (k*y) hdkg
    have hBtwo := Nat.mul_le_mul_left (2*k*g) hdksq
    have hScaledY := Nat.mul_lt_mul_of_pos_left hsumY (show 0 < k^2*g by positivity)
    nlinarith only [hBd,hBy,hBtwo,hScaledY]
  have hzscale := Nat.mul_lt_mul_of_pos_left hscale (show 0 < k*y^2 by positivity)
  have hcross : (D+k*y)*(k*(g+y*z)+D) < (k*y*q)*(k*(g+y*z)+D) := by
    have hqscale := congrArg (fun n => k*y*n) hmatch
    nlinarith only [hzscale,hsmall,hqscale]
  exact Nat.lt_of_mul_lt_mul_right hcross

private theorem quotient_eq_of_interval {D s q : ℕ} (hs : 0 < s)
    (hlo : D+s < s*q) (hhi : s*q < D+2*s) : q = D/s+2 := by
  have hlow : s*(D/s) ≤ D := Nat.mul_div_le D s
  have hhigh : D < s*(D/s+1) := by
    nlinarith only [Nat.div_add_mod D s, Nat.mod_lt D hs]
  have hqlo : D/s+2 ≤ q := by
    by_contra! hn
    have h := Nat.mul_le_mul_left s (show q ≤ D/s+1 by omega)
    nlinarith only [h,hlo,hlow]
  have hqhi : q ≤ D/s+2 := by
    by_contra! hn
    have h := Nat.mul_le_mul_left s (show D/s+3 ≤ q by omega)
    nlinarith only [h,hhi,hhigh]
  omega

private theorem cofactor_gap_bound {g y z q k D : ℕ}
    (hg : 0 < g) (hy : 0 < y) (ho : g*y ≤ z) (hq : 5 ≤ q)
    (he : (g*y+z)^2 = q*((g*y+1)*(z+1)))
    (hscale : k*(z+g*y) < g*D) (hlo : D+k*y < k*y*q) :
    let w := k*y*(q-1)-D
    0 < w ∧ (q-3)*w < k*y := by
  let w := k*y*(q-1)-D
  have ha := Nat.mul_add (k*y) (q-1) 1
  rw [show q-1+1=q by omega, mul_one] at ha
  have hw : w+D=k*y*(q-1) := by
    dsimp [w]
    exact Nat.sub_add_cancel (by omega)
  have hwpos : 0 < w := by omega
  have hz : 0 < z := lt_of_lt_of_le (Nat.mul_pos hg hy) ho
  have hden : (g*y)*z < (g*y+1)*(z+1) := by nlinarith
  have hqcomp := Nat.mul_lt_mul_of_pos_left hden (show 0 < q by omega)
  rw [← he] at hqcomp
  have hgyz := Nat.mul_le_mul_left (g*y) ho
  have hg1 : (q-3)*(g*y)*z < z*z := by
    have hsub := congrArg (fun n => n*(g*y)*z) (show q-3+3=q by omega)
    nlinarith only [hsub,hqcomp,hgyz]
  have hg2 := Nat.lt_of_mul_lt_mul_right hg1
  have hscaledq := Nat.mul_lt_mul_of_pos_left hqcomp (show 0 < k*y by
    have : 0 < k := by
      by_contra! h
      have hk0 : k=0 := by omega
      simp [hk0] at hlo
    positivity)
  have hscaledz := Nat.mul_lt_mul_of_pos_left hscale (Nat.mul_pos hy hz)
  have hbetter : (w*z)*(g*y) < (k*g*y^2)*(g*y) := by
    have hWscaled := congrArg (fun n => n*(g*y*z)) hw
    have hAscaled := congrArg (fun n => n*(g*y*z)) ha
    nlinarith only [hscaledq,hscaledz,hWscaled,hAscaled]
  have hWz := Nat.lt_of_mul_lt_mul_right hbetter
  have hWq := Nat.mul_lt_mul_of_pos_left hg2 hwpos
  have hWend : ((q-3)*w)*(g*y) < (k*y)*(g*y) := by
    nlinarith only [hWz,hWq]
  exact ⟨hwpos, Nat.lt_of_mul_lt_mul_right hWend⟩

private theorem quadratic_polynomial_contradiction {g y : ℤ}
    (hy : 33 ≤ y) (hg : 2 ≤ g)
    (hpoly : g^2 + (y*(y^2-1)-1) = ((y-1)*(y^2-1))*g) : False := by
  let D := y^2-1
  let A := (y-1)*D
  let B := y*D-1
  have hD : 1 ≤ D := by dsimp [D]; nlinarith
  have hA : 4 ≤ A := by dsimp [A,D]; nlinarith
  have hAD : 3 ≤ A-D := by dsimp [A,D]; nlinarith
  have hrel : B+1=A+D := by dsimp [A,B,D]; ring
  have hBgt : A-1 < B := by nlinarith [hrel,hD]
  have hB2 : B < 2*(A-2) := by nlinarith [hrel,hAD]
  have hgle : g < A := by
    by_contra h
    have hge : A≤g := by omega
    have hprod : A*g≤g*g := mul_le_mul_of_nonneg_right hge (by positivity)
    have hBpos : 0<B := by nlinarith [hBgt,hA]
    nlinarith [hpoly]
  by_cases hnear : g=A-1
  · rw [hnear] at hpoly
    nlinarith [hBgt]
  · have hfar : g≤A-2 := by omega
    have hprod : 2*(A-2)≤g*(A-g) := by
      have hfactor := mul_nonneg (show (0:ℤ)≤g-2 by omega)
        (show (0:ℤ)≤A-g-2 by omega)
      nlinarith [hfactor]
    nlinarith [hpoly,hprod,hB2]

theorem cofactor_one_int {g y z q : ℤ}
    (hy : 33 ≤ y) (hg : 2 ≤ g) (hq : q=y+1)
    (hquot : q*(g+y*z+(y^2-1))=(y^2-1)*(g*y+z))
    (hlcm : (g+y*z)*(g*y+z)=(y^2-1)*(g*y*z+1)) : False := by
  have hy1 : 1<y := by omega
  have hD : (y^2-1)=(y-1)*(y+1) := by ring
  have hcancel : g+y*z+(y^2-1)=(y-1)*(g*y+z) := by
    apply mul_left_cancel₀ (by omega : (y+1)≠0)
    calc
      (y+1)*(g+y*z+(y^2-1)) = q*(g+y*z+(y^2-1)) := by rw [hq]
      _ = (y^2-1)*(g*y+z) := hquot
      _ = (y+1)*((y-1)*(g*y+z)) := by rw [hD]; ring
  have hz : z+(y^2-1)=g*(y^2-y-1) := by nlinarith only [hcancel]
  have hS2 : g*y+z=(y^2-1)*(g-1) := by
    have hgz := congrArg (fun t : ℤ => g*t) hD
    nlinarith only [hz,hD,hgz]
  have hS1 : g+y*z=(y^2-1)*(g*(y-1)-y) := by
    have hyz := congrArg (fun t : ℤ => y*t) hz
    have hgy := congrArg (fun t : ℤ => g*(y-1)*t) hD
    nlinarith only [hz,hD,hyz,hgy]
  have hcancelD : (y^2-1)*((g*(y-1)-y)*(g-1))=g*y*z+1 := by
    have hlcm' : (y^2-1)*((y^2-1)*((g*(y-1)-y)*(g-1))) =
        (y^2-1)*(g*y*z+1) := by
      calc
        _ = ((y^2-1)*(g*(y-1)-y))*((y^2-1)*(g-1)) := by ring
        _ = (g+y*z)*(g*y+z) := by rw [hS1,hS2]
        _ = (y^2-1)*(g*y*z+1) := hlcm
    exact mul_left_cancel₀ (by nlinarith [hy] : (y^2-1)≠0) hlcm'
  have hyz' := congrArg (fun t : ℤ => g*y*t) hz
  have hD' := congrArg (fun t : ℤ => g^2*(y-1)*t) hD
  have hpoly : g^2 + (y*(y^2-1)-1) = ((y-1)*(y^2-1))*g := by
    nlinarith only [hcancelD,hyz',hD',hD]
  exact quadratic_polynomial_contradiction hy hg hpoly

end CrystalFullGcdSplit

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ g y z d q k : ℕ,
    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    0 < d → d < 2*(y-1) → d % 2 = 0 →
    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →
    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →
    5 ≤ q → (g*y+z)^2=q*((g*y+1)*(z+1)) →
    g.Coprime y → g.Coprime z → y.Coprime z →
    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →
    Nat.gcd (g+y*z) (g*y+z)=y^2-1 →
    z<g*(y^2-1) → y*q<(y^2-1)+3*y →
    Odd k → 3≤k → (g+y*z).lcm (g*y+z)*k=g*y*z+1 →
    k*(z+g*y)<g*(y^2-1) →
    (y^2-1)+k*y<k*y*q → k*y*q<(y^2-1)+2*k*y →
    q=(y^2-1)/(k*y)+2 →
    (q-3)*(k*y*(q-1)-(y^2-1))<k*y → k∣y → False

def H2 : Prop :=
  ∀ g y z d q k : ℕ,
    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    0 < d → d < 2*(y-1) → d % 2 = 0 →
    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →
    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →
    5 ≤ q → (g*y+z)^2=q*((g*y+1)*(z+1)) →
    g.Coprime y → g.Coprime z → y.Coprime z →
    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →
    Nat.gcd (g+y*z) (g*y+z)=y^2-1 →
    z<g*(y^2-1) → y*q<(y^2-1)+3*y →
    Odd k → 3≤k → (g+y*z).lcm (g*y+z)*k=g*y*z+1 →
    k*(z+g*y)<g*(y^2-1) →
    (y^2-1)+k*y<k*y*q → k*y*q<(y^2-1)+2*k*y →
    q=(y^2-1)/(k*y)+2 →
    (q-3)*(k*y*(q-1)-(y^2-1))<k*y →
    ¬ k∣y → q≤k+2 → False

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 →
    OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro hDivY hNotDivY g y z d q hg hy hgo hyo hzo ho hdiv hd hdup hde hgd hgd'
    hq hquot hgy hgz hyz hfirst hsecond hD hzb hqbd
  have hg2 : 2 ≤ g := hg
  have hy2 : 2 ≤ y := by omega
  have hgy2 : 1 < g*y := by nlinarith [Nat.mul_le_mul hg2 hy2]
  have hz2 : 1 < z := by omega
  have hkA : 0 < g*y+z := by positivity
  have hkB : 0 < g+y*z := by positivity
  obtain ⟨k,hk⟩ := Nat.lcm_dvd hfirst hsecond
  have hkpos : 0 < k := by
    by_contra! hk0
    have he : k=0 := by omega
    simp [he] at hk
  obtain ⟨r,hrOdd,hrN,_⟩ := CrystalVieta.odd_crystal_factor (hgo.mul hyo) hzo
    hgy2 hz2 (by omega) hquot
  have hkOdd : Odd k := by
    obtain ⟨u,hu⟩ := Nat.dvd_lcm_right (g+y*z) (g*y+z)
    have hcancel : (g*y+z)*r=(g*y+z)*(u*k) := by
      calc
        (g*y+z)*r=g*y*z+1 := hrN
        _=((g+y*z).lcm (g*y+z))*k := hk
        _=(g*y+z)*(u*k) := by rw [hu]; ring
    have hrk : r=u*k := Nat.eq_of_mul_eq_mul_left hkA hcancel
    exact hrOdd.of_dvd_nat ⟨u, by simpa [Nat.mul_comm] using hrk⟩
  let D := y^2-1
  have hD : Nat.gcd (g+y*z) (g*y+z)=D := by simpa [D] using hD
  have hDadd : D+1=y*y := by
    dsimp [D]
    rw [pow_two]
    exact Nat.sub_add_cancel (by nlinarith)
  have hp : k*((g+y*z)*(g*y+z))=D*(g*y*z+1) := by
    calc
      k*((g+y*z)*(g*y+z)) = k*(Nat.gcd (g+y*z) (g*y+z)*((g+y*z).lcm (g*y+z))) := by
        rw [Nat.gcd_mul_lcm]
      _=D*((g+y*z).lcm (g*y+z)*k) := by rw [hD]; ring
      _=D*(g*y*z+1) := by rw [← hk]
  have hgY := CrystalFullGcdSplit.first_component_bound hg2 ho hfirst
  obtain ⟨hscale,hupper⟩ := CrystalFullGcdSplit.scaled_bounds hg2 hy2 ho hgY
    (by omega) hkpos hp (by omega) hquot
  have hlo := CrystalFullGcdSplit.scaled_quotient_lower hg2 (by omega)
    (by omega) hkpos hgY (by omega) hscale hp hrN hquot
  have hlo' : D+k*y < (k*y)*q := by simpa [Nat.mul_assoc] using hlo
  have hupper' : (k*y)*q < D+2*(k*y) := by simpa [Nat.mul_assoc] using hupper
  have hqExact := CrystalFullGcdSplit.quotient_eq_of_interval (by positivity) hlo' hupper'
  obtain ⟨hwpos,hgap⟩ := CrystalFullGcdSplit.cofactor_gap_bound
    (by omega) (by omega) ho hq hquot hscale hlo
  have hmatch : q*(k*(g+y*z)+D)=D*(g*y+z) := by
    have hden : (g*y+1)*(z+1)=(g*y+z)*(r+1) := by nlinarith only [hrN]
    have hq' : g*y+z=q*(r+1) := by
      apply Nat.eq_of_mul_eq_mul_left hkA
      rw [hden] at hquot
      nlinarith only [hquot]
    have hr' : k*(g+y*z)=D*r := by
      apply Nat.eq_of_mul_eq_mul_left hkA
      nlinarith only [hp,congrArg (D*·) hrN]
    rw [hr']
    nlinarith only [congrArg (D*·) hq']
  by_cases hk1 : k=1
  · subst k
    have hqY : q=y+1 := by
      have hlow : D+y<y*q := by simpa [D] using hlo
      have hhigh : y*q<D+2*y := by simpa [D] using hupper
      have hqlo : y+1≤q := by
        by_contra! hn
        have hmul := Nat.mul_le_mul_left y (show q≤y by omega)
        nlinarith only [hDadd,hlow,hmul]
      have hqhi : q≤y+1 := by
        by_contra! hn
        have hmul := Nat.mul_le_mul_left y (show y+2≤q by omega)
        nlinarith only [hDadd,hhigh,hmul]
      omega
    have hYsqPos : 1≤y^2 := by nlinarith only [hy]
    have hcastSub : ((y^2-1:ℕ):ℤ)=(y:ℤ)^2-1 := by
      rw [Nat.cast_sub hYsqPos, Nat.cast_pow]
      rfl
    have hmatch' : q*(g+y*z+(y^2-1))=(y^2-1)*(g*y+z) := by
      simpa [D] using hmatch
    have hp' : (g+y*z)*(g*y+z)=(y^2-1)*(g*y*z+1) := by
      simpa [D] using hp
    have hyZ : (33 : ℤ) ≤ y := by exact_mod_cast hy
    have hgZ : (2 : ℤ) ≤ g := by exact_mod_cast hg2
    have hqYZ : (q : ℤ)=(y:ℤ)+1 := by exact_mod_cast hqY
    have hmZ : (q:ℤ)*((g:ℤ)+(y:ℤ)*(z:ℤ)+((y:ℤ)^2-1))=
        ((y:ℤ)^2-1)*((g:ℤ)*(y:ℤ)+(z:ℤ)) := by
      have hc := congrArg (fun n : ℕ => (n : ℤ)) hmatch'
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hcastSub] using hc
    have hpZ : ((g:ℤ)+(y:ℤ)*(z:ℤ))*((g:ℤ)*(y:ℤ)+(z:ℤ))=
        ((y:ℤ)^2-1)*((g:ℤ)*(y:ℤ)*(z:ℤ)+1) := by
      have hc := congrArg (fun n : ℕ => (n : ℤ)) hp'
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hcastSub] using hc
    exact CrystalFullGcdSplit.cofactor_one_int hyZ hgZ hqYZ hmZ hpZ
  · have hk3 : 3 ≤ k := by
      obtain ⟨j,hj⟩ := hkOdd
      omega
    by_cases hky : k∣y
    · exact hDivY g y z d q k hg hy hgo hyo hzo ho hdiv hd hdup hde hgd hgd'
        hq hquot hgy hgz hyz hfirst hsecond hD hzb hqbd hkOdd hk3 hk.symm hscale hlo
        hupper hqExact hgap hky
    · have hw : k*y*(q-1)-D + D=k*y*(q-1) := by
        dsimp [D]
        omega
      have hmodD : D%y=y-1 := by
        have hres := congrArg (fun n => n%y) hDadd
        have hylt : 1<y := by omega
        have hprod : (y*y)%y=0 := by simp
        have hDplus : (D%y+1)%y=0 := by
          simpa [Nat.add_mod, hprod, Nat.mod_eq_of_lt hylt] using hres
        exact CrystalFullGcdSplit.mod_succ_zero hylt hDplus
      have hprodmod : (k*y*(q-1))%y=0 := by
        have hkyMod : (k*y)%y=0 := by
          rw [Nat.mul_comm k y, Nat.mul_mod_right]
        rw [Nat.mul_mod, hkyMod]
        simp
      have hwmod : (k*y*(q-1)-D)%y=1 := by
        have hres := congrArg (fun n => n%y) hw
        have hylt : 1<y := by omega
        have hleft : ((k*y*(q-1)-D)%y+D%y)%y=0 := by
          simpa [Nat.add_mod, hprodmod, hmodD, Nat.mod_eq_of_lt hylt] using hres
        have hWlt : (k*y*(q-1)-D)%y<y := Nat.mod_lt _ (by omega)
        have hleft' : ((k*y*(q-1)-D)%y+(y-1))%y=0 := by
          simpa [hmodD] using hleft
        exact CrystalFullGcdSplit.mod_predecessor_zero hylt hWlt hleft'
      have hwne : k*y*(q-1)-D ≠ 1 := by
        intro hwone
        have heq : y*y=y*(k*(q-1)) := by
          have h := hw
          rw [hwone] at h
          calc
            y*y = D+1 := hDadd.symm
            _ = k*y*(q-1) := by omega
            _ = y*(k*(q-1)) := by ring
        have heq' : y=k*(q-1) := Nat.eq_of_mul_eq_mul_left (by omega) heq
        exact hky ⟨q-1, heq'⟩
      have hwlarge : y+1≤k*y*(q-1)-D := by
        by_contra! hn
        have hwle : k*y*(q-1)-D≤y := by omega
        rcases lt_or_eq_of_le hwle with hlt | heq
        · rw [Nat.mod_eq_of_lt hlt] at hwmod
          exact hwne (by omega)
        · rw [heq, Nat.mod_self] at hwmod
          omega
      have hqbound : q≤k+2 := by
        by_contra! hn
        have hksub : k≤q-3 := by omega
        have hmul := Nat.mul_le_mul_right (y+1) hksub
        have hwscale := Nat.mul_le_mul_left (q-3) hwlarge
        nlinarith only [hmul,hwscale,hgap]
      exact hNotDivY g y z d q k hg hy hgo hyo hzo ho hdiv hd hdup hde hgd hgd'
        hq hquot hgy hgz hyz hfirst hsecond hD hzb hqbd hkOdd hk3 hk.symm hscale hlo
        hupper hqExact hgap hky hqbound

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1
