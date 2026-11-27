import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1

/-! The common multiple of the two component sums has an odd least-common-multiple
cofactor. Accounting for that cofactor and the linear term of the product gives
a stronger quotient bound in both remaining cases. -/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1

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
  have hsumY : 2*y^2+2*y < y^3 := by
    nlinarith only [hyprod,hycube]
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
    (hlo : D+s < s*q) (hhi : s*q < D+2*s) :
    q = D/s+2 := by
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

private theorem quotient_le_cofactor_product {y q k D m : ℕ} (hy : 2 ≤ y)
    (hq : 5 ≤ q) (hm : 2 ≤ m) (hD : y^2-1=D*m)
    (hWpos : 0 < k*y*(q-1)-D) (hgap : (q-3)*(k*y*(q-1)-D)<k*y) :
    q ≤ m*k+2 := by
  let w := k*y*(q-1)-D
  change 0 < w at hWpos
  change (q-3)*w < k*y at hgap
  have hw : w+D=k*y*(q-1) := Nat.sub_add_cancel (by
    dsimp [w] at hWpos
    omega)
  have hD' : D*m+1=y^2 := by
    have hy2 : 1 ≤ y^2 := by nlinarith
    omega
  have hbalance : m*w+y*y=1+y*(m*k*(q-1)) := by
    nlinarith only [congrArg (m*·) hw,hD']
  have hres := congrArg (fun n => n % y) hbalance
  have hres' : (m*w)%y=1 := by
    have hy1 : 1 % y = 1 := Nat.mod_eq_of_lt (by omega)
    simpa [Nat.add_mul_mod_self_left, hy1] using hres
  have hWlarge : y+1 ≤ m*w := by
    by_contra! hn
    rcases lt_or_eq_of_le (show m*w ≤ y by omega) with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt] at hres'
      have hmw := Nat.mul_le_mul_left m (show 1 ≤ w by omega)
      omega
    · rw [heq, Nat.mod_self] at hres'
      omega
  have hl := Nat.mul_le_mul_right (q-3) hWlarge
  have hstrict := Nat.mul_lt_mul_of_pos_left hgap (show 0 < m by omega)
  by_contra! hn
  have hqsub : q-3+3=q := by omega
  have hqbound : m*k ≤ q-3 := by omega
  have hmul := Nat.mul_le_mul_right y hqbound
  nlinarith only [hl,hstrict,hmul,Nat.zero_le (q-3)]

private theorem quotient_square_bound {y q k D m : ℕ} (hq : 2 ≤ q)
    (hm : 0 < m) (hD : D*m < y^2) (hupper : k*y*q < D+2*k*y)
    (hcofactor : q ≤ m*k+2) : (q-2)^2 < y := by
  have hsub : q-2+2=q := by omega
  have hs := congrArg (fun n => k*y*n) hsub
  have hu : k*y*(q-2) < D := by nlinarith only [hupper,hs]
  have hm' := Nat.mul_lt_mul_of_pos_right hu hm
  have hsuble : q-2 ≤ m*k := by omega
  have hscaled := Nat.mul_le_mul_right (y*(q-2)) hsuble
  have hh : (q-2)^2*y < y*y := by nlinarith only [hD,hm',hscaled]
  exact Nat.lt_of_mul_lt_mul_right hh

/-- The product plus one is the least common multiple of the two sums. -/
def H1 : Prop :=
  ∀ g y z d q : ℕ,
    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    0 < d → d < 2*(y-1) → d % 2 = 0 →
    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →
    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →
    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →
    g.Coprime y → g.Coprime z → y.Coprime z →
    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →
    let D := Nat.gcd (g+y*z) (g*y+z)
    D ∣ y^2-1 → D < y^2-1 →
    (g+y*z).lcm (g*y+z) = g*y*z+1 →
    z+g*y < g*D → D+y < y*q → y*q < D+2*y → q = D/y+2 → (q-3)*(y*(q-1)-D) < y →
    q ≤ (y^2-1)/D+2 → (q-2)^2 < y → 2*q ≤ y+3 → False

/-- The product plus one is an odd multiple of the least common multiple,
with cofactor at least three. -/
def H2 : Prop :=
  ∀ g y z d q k : ℕ,
    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    0 < d → d < 2*(y-1) → d % 2 = 0 →
    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →
    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →
    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →
    g.Coprime y → g.Coprime z → y.Coprime z →
    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →
    let D := Nat.gcd (g+y*z) (g*y+z)
    D ∣ y^2-1 → D < y^2-1 →
    Odd k → 3 ≤ k → (g+y*z).lcm (g*y+z)*k = g*y*z+1 →
    k*(z+g*y) < g*D → D+k*y < k*y*q → k*y*q < D+2*k*y →
    q = D/(k*y)+2 → (q-3)*(k*y*(q-1)-D) < k*y →
    q ≤ ((y^2-1)/D)*k+2 → (q-2)^2 < y → 3*k*y < D →
    6*q ≤ y+11 → False

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro hOne hMany g y z d q hg hy hgo hyo hzo ho hcr hd hdb hde hdc hdc'
    hq hquot hgy hgz hyz hfirst hsecond
  let D := Nat.gcd (g+y*z) (g*y+z)
  change D ∣ y^2-1 → D < y^2-1 → z < g*D → y*q < D+3*y → 2*q ≤ y+5 → False
  intro hDd hDl _ _ _
  have hg2 : 2 ≤ g := hg
  have hy2 : 2 ≤ y := by omega
  have hgy2 : 1 < g*y := by nlinarith
  have hz2 : 1 < z := by omega
  obtain ⟨k,hk⟩ := Nat.lcm_dvd hfirst hsecond
  have hkpos : 0 < k := by
    by_contra! hk0
    have he : k=0 := by omega
    simp [he] at hk
  obtain ⟨r,hr,he,_⟩ := CrystalVieta.odd_crystal_factor (hgo.mul hyo) hzo
    hgy2 hz2 (by omega) hquot
  have hkodd : Odd k := by
    obtain ⟨u,hu⟩ := Nat.dvd_lcm_right (g+y*z) (g*y+z)
    have hcancel : (g*y+z)*r=(g*y+z)*(u*k) := by
      calc
        (g*y+z)*r = g*y*z+1 := he
        _ = ((g+y*z).lcm (g*y+z))*k := hk
        _ = (g*y+z)*(u*k) := by rw [hu, mul_assoc]
    have hrk : r=u*k := Nat.eq_of_mul_eq_mul_left (by omega) hcancel
    exact hr.of_dvd_nat ⟨u, by simpa [Nat.mul_comm] using hrk⟩
  have hp : k*((g+y*z)*(g*y+z))=D*(g*y*z+1) := by
    calc
      k*((g+y*z)*(g*y+z))=k*(D*((g+y*z).lcm (g*y+z))) := by
        rw [Nat.gcd_mul_lcm]
      _ = D*((g+y*z).lcm (g*y+z)*k) := by ring
      _ = D*(g*y*z+1) := by rw [← hk]
  have hgY := first_component_bound hg2 ho hfirst
  obtain ⟨hzB,hqB⟩ := scaled_bounds hg2 hy2 ho hgY hDl.le hkpos hp (by omega) hquot
  obtain ⟨m,hm⟩ := hDd
  have hDpos : 0 < D := Nat.gcd_pos_of_pos_left _ (by positivity)
  have hqLower := scaled_quotient_lower hg2 (by omega) (by omega) hkpos hgY hDl.le hzB hp he hquot
  have hquotExact := quotient_eq_of_interval (show 0 < k*y by positivity) hqLower (by
    nlinarith only [hqB])
  have hm2 : 2 ≤ m := by
    by_contra! h
    interval_cases m <;> simp_all
  have hy2sq : 2*D < y^2 := by
    have hm' := Nat.mul_le_mul_left D hm2
    have hsub : y^2-1 < y^2 := by
      have : 1 ≤ y^2 := by nlinarith
      omega
    nlinarith only [hm',hm,hsub]
  obtain ⟨hWpos,hGap⟩ := cofactor_gap_bound (show 0 < g by omega)
    (show 0 < y by omega) ho hq hquot hzB hqLower
  have hcof : (y^2-1)/D=m := by rw [hm, Nat.mul_div_cancel_left _ hDpos]
  have hQm := quotient_le_cofactor_product hy2 hq hm2 hm hWpos hGap
  have hDmul : D*m < y^2 := by omega
  have hqSquare := quotient_square_bound (by omega) (by omega) hDmul hqB hQm
  rw [← hcof] at hQm
  by_cases hko : k=1
  · subst k
    simp only [mul_one,one_mul] at hk hzB hqB hqLower hquotExact hGap hQm
    have hqB' : 2*q ≤ y+3 := by
      by_contra! h
      have hh := Nat.mul_le_mul_left y (show y+4 ≤ 2*q by omega)
      nlinarith only [hh,hy2sq,hqB]
    exact hOne g y z d q hg hy hgo hyo hzo ho hcr hd hdb hde hdc hdc'
      hq hquot hgy hgz hyz hfirst hsecond ⟨m,hm⟩ hDl hk.symm hzB hqLower hqB hquotExact hGap hQm hqSquare hqB'
  · have hThree : 3 ≤ k := by
      obtain ⟨j,hj⟩ := hkodd
      omega
    have hqB' : 6*q ≤ y+11 := by
      by_contra! h
      have hh := Nat.mul_le_mul_left y (show y+12 ≤ 6*q by omega)
      have hmul := Nat.mul_le_mul_left (y*(q-2)) hThree
      have hqsub : q-2+2=q := by omega
      have e3 : 3*y*(q-2)+6*y=3*y*q := by
        calc
          _ = 3*y*(q-2+2) := by ring
          _ = _ := by rw [hqsub]
      have ek : k*y*(q-2)+2*k*y=k*y*q := by
        calc
          _ = k*y*(q-2+2) := by ring
          _ = _ := by rw [hqsub]
      nlinarith only [hh,hmul,hy2sq,hqB,e3,ek]
    have hDlarge : 3*k*y < D := by
      have hh := Nat.mul_le_mul_left (k*y) hq
      nlinarith only [hh,hqB]
    exact hMany g y z d q k hg hy hgo hyo hzo ho hcr hd hdb hde hdc hdc'
      hq hquot hgy hgz hyz hfirst hsecond ⟨m,hm⟩ hDl hkodd hThree hk.symm hzB hqLower hqB hquotExact hGap hQm hqSquare hDlarge hqB'

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1
