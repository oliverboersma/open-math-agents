import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1

/-! Bound the second quotient of the shared-factor pair by the gcd of the two sums. -/

namespace CrystalVieta

theorem quotient_residues {q : ℕ} (hq : 2 ≤ q) :
    ∀ u v : ℕ, 0 < u → u ≤ v → (u+v-1)^2 = q*u*v →
      (u % q = 1 ∧ v % q = 0) ∨ (u % q = 0 ∧ v % q = 1) := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro v hu huv heq
    by_cases hu1 : u = 1
    · subst u
      have hvPos : 0 < v := by omega
      have he : v*v = q*v := by simpa [pow_two] using heq
      have hvq : v = q := Nat.eq_of_mul_eq_mul_right hvPos (by simpa [Nat.mul_comm] using he)
      subst v
      left
      constructor
      · exact Nat.mod_eq_of_lt (by omega)
      · simp
    · have hu2 : 2 ≤ u := by omega
      let w : ℤ := ((q : ℤ)-2)*u+2-v
      have huvpos : 1 ≤ u+v := by omega
      have heqZ : ((u : ℤ)+(v : ℤ)-1)^2 = (q : ℤ)*u*v := by
        have hc := congrArg (fun n : ℕ => (n : ℤ)) heq
        simpa only [Nat.cast_pow, Nat.cast_sub huvpos, Nat.cast_add, Nat.cast_one,
          Nat.cast_mul] using hc
      have hwprod : (v : ℤ)*w = ((u : ℤ)-1)^2 := by
        dsimp [w]
        nlinarith [heqZ]
      have hvZ : 0 < (v : ℤ) := by exact_mod_cast (show 0 < v by omega)
      have huZ : 2 ≤ (u : ℤ) := by exact_mod_cast hu2
      have hwpos : 0 < w := by nlinarith [hwprod]
      have hwlt : w < u := by
        by_contra h
        have huw : (u : ℤ) ≤ w := by omega
        have huuv : (u : ℤ)*(u : ℤ) ≤ (u : ℤ)*(v : ℤ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast huv) (by positivity)
        have huwprod : (u : ℤ)*(v : ℤ) ≤ w*(v : ℤ) :=
          mul_le_mul_of_nonneg_right huw (by positivity)
        nlinarith [hwprod]
      have hwCast : (w.toNat : ℤ) = w := Int.toNat_of_nonneg (le_of_lt hwpos)
      have hwNatPos : 0 < w.toNat := by
        have hwNatPosZ : (0 : ℤ) < (w.toNat : ℤ) := by rw [hwCast]; exact hwpos
        exact_mod_cast hwNatPosZ
      have hwNatLt : w.toNat < u := by
        have hwNatLtZ : (w.toNat : ℤ) < u := by rw [hwCast]; exact hwlt
        exact_mod_cast hwNatLtZ
      have hnewZ : (w+(u : ℤ)-1)^2 = (q : ℤ)*w*u := by
        dsimp [w]
        nlinarith [heqZ]
      have hNatCast : ((w.toNat+u-1 : ℕ) : ℤ) = (w.toNat : ℤ)+(u : ℤ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ w.toNat+u)]
        simp only [Nat.cast_add, Nat.cast_one]
      have hnewZ' : ((w.toNat+u-1 : ℕ) : ℤ)^2 =
          (q : ℤ)*(w.toNat : ℤ)*u := by
        calc
          _ = ((w.toNat : ℤ)+(u : ℤ)-1)^2 := by rw [hNatCast]
          _ = (w+(u : ℤ)-1)^2 := by rw [hwCast]
          _ = (q : ℤ)*w*u := hnewZ
          _ = (q : ℤ)*(w.toNat : ℤ)*u := by nlinarith [hwCast]
      have hnew : (w.toNat+u-1)^2 = q*w.toNat*u := by exact_mod_cast hnewZ'
      have hres := ih w.toNat hwNatLt u hwNatPos (Nat.le_of_lt hwNatLt) hnew
      have hsum : (w.toNat : ℕ)+v+2*u = q*u+2 := by
        dsimp [w] at hwCast
        have hwCastN : (w.toNat : ℤ) = ((q : ℤ)-2)*u+2-v := hwCast
        have hwCastN' : ((w.toNat : ℕ) : ℤ) + v + 2*u = (q : ℤ)*u+2 := by
          nlinarith [hwCastN]
        exact_mod_cast hwCastN'
      have hmod0 : (w.toNat+v+2*u) % q = 2 % q := by
        rw [hsum]
        simp [Nat.add_mod]
      have hmod : (((w.toNat % q)+(v % q)+2*(u % q)) % q) = 2 % q := by
        simpa [Nat.add_mod] using hmod0
      rcases hres with ⟨hwu, huv0⟩ | ⟨hwu0, huv1⟩
      · right
        have hv1 : v % q = 1 := by
          rw [hwu, huv0] at hmod
          simp only [Nat.add_zero, Nat.mul_zero] at hmod
          have hxlt : v % q < q := Nat.mod_lt _ (by omega)
          by_cases hq2 : q = 2
          · subst q
            norm_num at hmod
            omega
          · have hq3 : 3 ≤ q := by omega
            have hq2mod : 2 % q = 2 := Nat.mod_eq_of_lt (by omega)
            rw [hq2mod] at hmod
            have hmod1 : (1+v%q)%q = 2 := hmod
            by_cases hlt : 1+v%q < q
            · rw [Nat.mod_eq_of_lt hlt] at hmod1
              omega
            · have hx : 1+v%q=q := by omega
              rw [hx, Nat.mod_self] at hmod1
              omega
        exact ⟨huv0, hv1⟩
      · left
        have hv0 : v % q = 0 := by
          rw [hwu0, huv1] at hmod
          simp only [Nat.zero_add, Nat.mul_one] at hmod
          have hxlt : v % q < q := Nat.mod_lt _ (by omega)
          by_cases hq2 : q = 2
          · subst q
            norm_num at hmod
            omega
          · have hq3 : 3 ≤ q := by omega
            have hq2mod : 2 % q = 2 := Nat.mod_eq_of_lt (by omega)
            rw [hq2mod] at hmod
            have hmod1 : (v%q+2)%q = 2 := hmod
            by_cases hlt : v%q+2 < q
            · rw [Nat.mod_eq_of_lt hlt] at hmod1
              omega
            · have hqle : q ≤ v%q+2 := by omega
              have hqtop : v%q+2 ≤ q+1 := by omega
              by_cases heq : v%q+2=q
              · rw [heq, Nat.mod_self] at hmod1
                omega
              · have heq' : v%q+2=q+1 := by omega
                rw [heq'] at hmod1
                have hqplus : (q+1)%q=1 := by
                  rw [Nat.add_comm, Nat.add_mod_right 1 q]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hqplus] at hmod1
                omega
        exact ⟨huv1, hv0⟩

theorem quotient_sum_dvd {q u v : ℕ} (hq : 2 ≤ q) (hu : 0 < u)
    (huv : u ≤ v) (heq : (u+v-1)^2 = q*u*v) : q ∣ u+v-1 := by
  rcases quotient_residues hq u v hu huv heq with ⟨hu1,hv0⟩ | ⟨hu0,hv1⟩
  · have hsum : (u+v)%q = 1 := by
      rw [Nat.add_mod, hu1, hv0]
      exact Nat.mod_eq_of_lt (by omega)
    have hdecomp := Nat.mod_add_div (u+v) q
    rw [hsum] at hdecomp
    refine ⟨(u+v)/q, ?_⟩
    omega
  · have hsum : (u+v)%q = 1 := by
      rw [Nat.add_mod, hu0, hv1]
      exact Nat.mod_eq_of_lt (by omega)
    have hdecomp := Nat.mod_add_div (u+v) q
    rw [hsum] at hdecomp
    refine ⟨(u+v)/q, ?_⟩
    omega

theorem odd_crystal_factor {a b q : ℕ} (ha : Odd a) (hb : Odd b)
    (ha1 : 1 < a) (hb1 : 1 < b) (hq : 2 ≤ q)
    (heq : (a+b)^2 = q*((a+1)*(b+1))) :
    ∃ r : ℕ, Odd r ∧ (a+b)*r = a*b+1 ∧ r+1 ∣ a+b := by
  obtain ⟨x,hax⟩ := ha
  obtain ⟨y,hby⟩ := hb
  let u := x+1
  let v := y+1
  have hau : a+1=2*u := by dsimp [u]; omega
  have hbv : b+1=2*v := by dsimp [v]; omega
  have hu2 : 2 ≤ u := by dsimp [u]; omega
  have hv2 : 2 ≤ v := by dsimp [v]; omega
  have hsum : a+b=2*(u+v-1) := by omega
  have hquot : (u+v-1)^2=q*u*v := by
    have h := heq
    rw [hsum,hau,hbv] at h
    nlinarith [h]
  have hdiv : q ∣ u+v-1 := by
    by_cases huv : u ≤ v
    · exact quotient_sum_dvd hq (by omega) huv hquot
    · have hvu : v ≤ u := by omega
      have hquot' : (v+u-1)^2=q*v*u := by
        simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm] using hquot
      have hdiv' := quotient_sum_dvd hq (by omega) hvu hquot'
      simpa [Nat.add_comm] using hdiv'
  obtain ⟨k,hk⟩ := hdiv
  have hn : u+v=q*k+1 := by omega
  have hquot' : (q*k)^2=q*u*v := by rw [← hk]; exact hquot
  have hcancel : q*(q*k^2)=q*(u*v) := by
    calc
      q*(q*k^2)=(q*k)^2 := by ring
      _=q*u*v := hquot'
      _=q*(u*v) := by ring
  have hqPos : 0 < q := by omega
  have huvprod : u*v=q*k^2 := (Nat.eq_of_mul_eq_mul_left hqPos hcancel).symm
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k=0 := by omega
    rw [hk0] at hk
    omega
  let r := 2*k-1
  have hrplus : r+1=2*k := by dsimp [r]; omega
  have hrodd : Odd r := by
    refine ⟨k-1, ?_⟩
    dsimp [r]
    omega
  have hsum2 : a+b=2*q*k := by rw [hsum,hk]; ring
  have habprod : a*b+1=(a+b)*r := by
    dsimp [r]
    nlinarith [huvprod, hn, hau, hbv, hsum2]
  refine ⟨r, hrodd, habprod.symm, ?_⟩
  refine ⟨q, ?_⟩
  rw [hrplus, hsum2]
  ring

theorem coprime_of_crystal_factor {a b r : ℕ}
    (h : (a+b)*r=a*b+1) : Nat.Coprime a b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd a b
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hsum : g ∣ a+b := Nat.dvd_add hga hgb
  have hprod : g ∣ a*b := dvd_mul_of_dvd_left hga b
  have hsuccessor : g ∣ a*b+1 := by
    rw [← h]
    exact dvd_mul_of_dvd_left hsum r
  have hsuccessorZ : (g : ℤ) ∣ (a : ℤ)*(b : ℤ)+1 := by exact_mod_cast hsuccessor
  have hprodZ : (g : ℤ) ∣ (a : ℤ)*(b : ℤ) := by exact_mod_cast hprod
  have honeZ : (g : ℤ) ∣ 1 := by
    have hdiff : (g : ℤ) ∣ (a : ℤ)*(b : ℤ)+1-(a : ℤ)*(b : ℤ) :=
      dvd_sub hsuccessorZ hprodZ
    have hdiffEq : (a : ℤ)*(b : ℤ)+1-(a : ℤ)*(b : ℤ)=1 := by ring
    rw [hdiffEq] at hdiff
    exact hdiff
  have hone : g ∣ 1 := by exact_mod_cast honeZ
  exact Nat.dvd_one.mp hone

theorem shared_sum_gcd_bound {g y z : ℕ} (hg : 2 ≤ g) (hy : 2 ≤ y)
    (hcop : Nat.Coprime g z)
    (hfirst : g+y*z ∣ g*y*z+1) (hsecond : g*y+z ∣ g*y*z+1) :
    z < g*Nat.gcd (g+y*z) (g*y+z) ∧
      Nat.gcd (g+y*z) (g*y+z) ∣ y^2-1 := by
  let s₁ := g+y*z
  let s₂ := g*y+z
  let D := Nat.gcd s₁ s₂
  have hD1 : D ∣ s₁ := by dsimp [D]; exact Nat.gcd_dvd_left _ _
  have hD2 : D ∣ s₂ := by dsimp [D]; exact Nat.gcd_dvd_right _ _
  have hys₂ : D ∣ y*s₂ := dvd_mul_of_dvd_right hD2 y
  have hySq : 1 ≤ y^2 := by nlinarith [hy]
  have hgGrow : g ≤ g*y^2 := by
    calc
      g = g*1 := by omega
      _ ≤ g*y^2 := Nat.mul_le_mul_left g hySq
  have hs₁le : s₁ ≤ y*s₂ := by
    dsimp [s₁,s₂]
    calc
      g+y*z ≤ g*y^2+y*z := Nat.add_le_add_right hgGrow _
      _ = y*(g*y+z) := by ring
  have hDg : D ∣ y*s₂-s₁ := Nat.dvd_sub hys₂ hD1
  have hdiff₁ : y*s₂-s₁ = g*(y^2-1) := by
    apply (Nat.sub_eq_iff_eq_add hs₁le).2
    calc
      y*s₂ = g*y^2+y*z := by dsimp [s₂]; ring
      _ = (g*y^2-g)+g+y*z := by rw [Nat.sub_add_cancel hgGrow]
      _ = g*(y^2-1)+s₁ := by
        rw [Nat.mul_sub_left_distrib]
        simp only [Nat.mul_one]
        dsimp [s₁]
        ring
  rw [hdiff₁] at hDg
  have hys₁ : D ∣ y*s₁ := dvd_mul_of_dvd_right hD1 y
  have hs₂le : s₂ ≤ y*s₁ := by
    dsimp [s₁,s₂]
    have hzGrow : z ≤ z*y^2 := by
      calc
        z = z*1 := by omega
        _ ≤ z*y^2 := Nat.mul_le_mul_left z hySq
    calc
      g*y+z ≤ g*y+z*y^2 := Nat.add_le_add_left hzGrow _
      _ = y*(g+y*z) := by ring
  have hDz : D ∣ y*s₁-s₂ := Nat.dvd_sub hys₁ hD2
  have hdiff₂ : y*s₁-s₂ = z*(y^2-1) := by
    apply (Nat.sub_eq_iff_eq_add hs₂le).2
    calc
      y*s₁ = g*y+y^2*z := by dsimp [s₁]; ring
      _ = (z*y^2-z)+g*y+z := by
        have hzGrow : z ≤ z*y^2 := by nlinarith [hy]
        have hcancel := Nat.sub_add_cancel hzGrow
        calc
          _ = g*y+(z*y^2-z+z) := by rw [hcancel]; ring
          _ = (z*y^2-z)+g*y+z := by omega
      _ = z*(y^2-1)+s₂ := by
        rw [Nat.mul_sub_left_distrib]
        simp only [Nat.mul_one]
        dsimp [s₂]
        ring
  rw [hdiff₂] at hDz
  have hDcommon : D ∣ Nat.gcd (g*(y^2-1)) (z*(y^2-1)) := Nat.dvd_gcd hDg hDz
  have hDtarget : D ∣ y^2-1 := by
    rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul] at hDcommon
    exact hDcommon
  have hy2pos : 0 < y^2-1 := by
    have hySq2 : 2 ≤ y^2 := by nlinarith [hy]
    omega
  have hDbound : D ≤ y^2-1 := Nat.le_of_dvd hy2pos hDtarget
  have hLcmDvd : s₁.lcm s₂ ∣ g*y*z+1 := Nat.lcm_dvd hfirst hsecond
  have hNpos : 0 < g*y*z+1 := by positivity
  have hLcmBound : s₁.lcm s₂ ≤ g*y*z+1 := Nat.le_of_dvd hNpos hLcmDvd
  have hprodLcm : D*(s₁.lcm s₂) = s₁*s₂ := by
    dsimp [D]
    exact Nat.gcd_mul_lcm s₁ s₂
  have hprodBound : s₁*s₂ ≤ D*(g*y*z+1) := by
    rw [← hprodLcm]
    exact Nat.mul_le_mul_left D hLcmBound
  have hDpos : 0 < D := by
    apply Nat.gcd_pos_of_pos_left
    dsimp [s₁]
    positivity
  have hzD : z < g*D := by
    by_contra hnot
    have hlarge : g*D ≤ z := by omega
    have hbase : D*(g*y*z) ≤ (y*z)*z := by
      calc
        D*(g*y*z) = (y*z)*(g*D) := by ring
        _ ≤ (y*z)*z := Nat.mul_le_mul_left (y*z) hlarge
    have hfactor : 1 ≤ g*z := by nlinarith [hg,hDpos]
    have hDlt : D < y^2+1 := by omega
    have hrest : D < (y^2+1)*(g*z) := by
      calc
        D < y^2+1 := hDlt
        _ ≤ (y^2+1)*(g*z) := by
          have h := Nat.mul_le_mul_left (y^2+1) hfactor
          simpa only [Nat.mul_one] using h
    have hexp : s₁*s₂ = (y*z)*z+(y^2+1)*(g*z)+g^2*y := by
      dsimp [s₁,s₂]
      ring
    have hrestLower : (y*z)*z+(y^2+1)*(g*z) ≤ s₁*s₂ := by
      rw [hexp]
      omega
    have hstrict : D*(g*y*z+1) < s₁*s₂ := by
      calc
        D*(g*y*z+1) = D*(g*y*z)+D := by ring
        _ ≤ (y*z)*z+D := Nat.add_le_add_right hbase D
        _ < (y*z)*z+(y^2+1)*(g*z) := Nat.add_lt_add_left hrest _
        _ ≤ s₁*s₂ := hrestLower
    omega
  exact ⟨hzD,hDtarget⟩

theorem quotient_times_y_gcd_bound {g y z q : ℕ} (hg : 2 ≤ g) (hy : 2 ≤ y)
    (hgy : g*y ≤ z) (hgz : z < g*Nat.gcd (g+y*z) (g*y+z))
    (hq : (g*y+z)^2=q*((g*y+1)*(z+1))) :
    y*q < Nat.gcd (g+y*z) (g*y+z)+3*y := by
  let D := Nat.gcd (g+y*z) (g*y+z)
  have hgpos : 0 < g := by omega
  have hypos : 0 < y := by omega
  have hzpos : 0 < z := lt_of_lt_of_le (Nat.mul_pos hgpos hypos) hgy
  have hqpos : 0 < q := by
    by_contra hn
    have : q=0 := by omega
    rw [this] at hq
    have hsq : 0 < (g*y+z)^2 := Nat.pow_pos (by omega : 0 < g*y+z)
    nlinarith
  have hDpos : 0 < D := by
    dsimp [D]
    apply Nat.gcd_pos_of_pos_left
    positivity
  have hDgz : z^2 < g*D*z := by
    have := Nat.mul_lt_mul_of_pos_right hgz hzpos
    nlinarith [this]
  have hgy2 : (g*y)^2 ≤ g*y*z := by
    have := Nat.mul_le_mul_left (g*y) hgy
    nlinarith [this]
  have hcross : y*(g*y+z)^2 < (D+3*y)*(g*y*z) := by
    nlinarith [hDgz, hgy2]
  have hden : g*y*z < (g*y+1)*(z+1) := by nlinarith
  have hqnum : q*((g*y+1)*(z+1)) = (g*y+z)^2 := hq.symm
  have hqgyz : q*(g*y*z) < (g*y+z)^2 := by
    have hmul := Nat.mul_lt_mul_of_pos_left hden hqpos
    calc
      q*(g*y*z) < q*((g*y+1)*(z+1)) := hmul
      _ = (g*y+z)^2 := hqnum
  have hqscaled : y*(q*(g*y*z)) < y*((g*y+z)^2) :=
    Nat.mul_lt_mul_of_pos_left hqgyz hypos
  have hcross' : y*(q*(g*y*z)) < (D+3*y)*(g*y*z) := by
    exact lt_trans hqscaled hcross
  have hfactorpos : 0 < g*y*z := Nat.mul_pos (Nat.mul_pos hgpos hypos) hzpos
  have hcancel : y*q < D+3*y := by
    by_contra hn
    have hle : D+3*y ≤ y*q := by omega
    have hmul := Nat.mul_le_mul_right (g*y*z) hle
    nlinarith [hcross']
  simpa [D] using hcancel

end CrystalVieta

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1

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
    Nat.gcd (g+y*z) (g*y+z) = y^2-1 →
    z < g*(y^2-1) → y*q < (y^2-1)+3*y → False

def H2 : Prop :=
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
    z < g*D → y*q < D+3*y → 2*q ≤ y+5 → False

theorem crystal_quotient_ge_two {a b q : ℕ} (ha : 1 < a) (hb : 1 < b)
    (heq : (a+b)^2 = q*((a+1)*(b+1))) : 2 ≤ q := by
  have hlt : (a+1)*(b+1) < (a+b)^2 := by
    calc
      _ < (a+b)*(b+1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ (a+b)*(a+b) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by rw [pow_two]
  by_contra! hq
  have hle := Nat.mul_le_mul_right ((a+1)*(b+1)) (show q ≤ 1 by omega)
  simp only [one_mul, ← heq] at hle
  omega

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro hFull hProper g y z d q hg hy hgo hyo hzo horder hdiv
    hd hdup hde hgd hgd' hq hqeq
  have hg2 : 2 ≤ g := hg
  have hy2 : 2 ≤ y := by omega
  have hgy4 : 4 ≤ g*y := Nat.mul_le_mul hg2 hy2
  have hz2 : 2 ≤ z := by omega
  have hyz4 : 4 ≤ y*z := Nat.mul_le_mul hy2 hz2
  obtain ⟨p,hpeq⟩ := hdiv
  have hpeq' : (g+y*z)^2 = p*((g+1)*(y*z+1)) := by
    simpa only [Nat.mul_comm] using hpeq
  obtain ⟨r,_,hr,_⟩ := CrystalVieta.odd_crystal_factor hgo (hyo.mul hzo)
    hg (by omega) (crystal_quotient_ge_two hg (by omega) hpeq') hpeq'
  obtain ⟨s,_,hs,_⟩ := CrystalVieta.odd_crystal_factor (hgo.mul hyo) hzo
    (by omega) (by omega) (by omega) hqeq
  have hc₁ : g.Coprime (y*z) := CrystalVieta.coprime_of_crystal_factor hr
  have hc₂ : (g*y).Coprime z := CrystalVieta.coprime_of_crystal_factor hs
  obtain ⟨hcy,hcz⟩ := Nat.coprime_mul_iff_right.mp hc₁
  have hyz : y.Coprime z := (Nat.coprime_mul_iff_left.mp hc₂).2
  have hfirst : g+y*z ∣ g*y*z+1 :=
    ⟨r, by simpa only [Nat.mul_assoc] using hr.symm⟩
  have hsecond : g*y+z ∣ g*y*z+1 := ⟨s, hs.symm⟩
  let D := Nat.gcd (g+y*z) (g*y+z)
  obtain ⟨hzD,hDdiv⟩ := CrystalVieta.shared_sum_gcd_bound hg2 hy2 hcz hfirst hsecond
  have hqD := CrystalVieta.quotient_times_y_gcd_bound hg2 hy2 horder hzD hqeq
  change z < g*D at hzD
  change D ∣ y^2-1 at hDdiv
  change y*q < D+3*y at hqD
  exfalso
  by_cases hfull : D = y^2-1
  · exact hFull g y z d q hg hy hgo hyo hzo horder ⟨p,hpeq⟩
      hd hdup hde hgd hgd' hq hqeq hcy hcz hyz hfirst hsecond hfull
      (by simpa only [hfull] using hzD) (by simpa only [hfull] using hqD)
  · have hypos : 0 < y^2-1 := by
      have hySq : 2 ≤ y^2 := by nlinarith [hy2]
      omega
    have hDlt : D < y^2-1 := lt_of_le_of_ne (Nat.le_of_dvd hypos hDdiv) hfull
    obtain ⟨k,hk⟩ := hDdiv
    have hk2 : 2 ≤ k := by
      by_contra! hsmall
      interval_cases k <;> simp at hk <;> omega
    have hDdouble : 2*D ≤ y^2-1 := by
      rw [hk, Nat.mul_comm 2]
      exact Nat.mul_le_mul_left D hk2
    have hqhalf : 2*q ≤ y+5 := by
      by_contra! hlarger
      have hyq : y*(y+6) ≤ y*(2*q) := Nat.mul_le_mul_left y (by omega)
      have hqDouble := Nat.mul_lt_mul_of_pos_left hqD (by decide : 0 < (2 : ℕ))
      have hsub := Nat.sub_le (y^2) 1
      nlinarith only [hyq,hqDouble,hDdouble,hsub]
    exact hProper g y z d q hg hy hgo hyo hzo horder ⟨p,hpeq⟩
      hd hdup hde hgd hgd' hq hqeq hcy hcz hyz hfirst hsecond ⟨k,hk⟩
      hDlt hzD hqD hqhalf

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1
