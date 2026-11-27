import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1

/-!
# Odd parameters in the normalized shared-divisor problem

Mixed parity is impossible in a positive pair with integral square quotient.
For two even components, shift each up by one. The shifted components are odd,
and replacing the larger root of the quotient quadratic by its Vieta partner
strictly decreases the smaller shifted component. The only odd base pair is
(1,1), which corresponds to zero components.
-/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1

theorem odd_shifted_eq_one (x : ℕ) :
    ∀ y q : ℕ, Odd x → Odd y → x ≤ y →
      ((x : ℤ) + y - 2)^2 = (q : ℤ)*x*y → x = 1 ∧ y = 1 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro y q hx hy hxy he
    have hxpos : 0 < x := by obtain ⟨k, hk⟩ := hx; omega
    have hypos : (0 : ℤ) < y := by exact_mod_cast (show 0 < y by omega)
    by_cases h1 : x = 1
    · subst x
      have hdiv : (y : ℤ) ∣ 1 := ⟨(q : ℤ) - y + 2, by
        push_cast at he
        linear_combination he⟩
      exact ⟨rfl, by exact_mod_cast (Int.eq_one_of_dvd_one hypos.le hdiv)⟩
    have hx3 : (3 : ℤ) ≤ x := by
      obtain ⟨k, hk⟩ := hx
      exact_mod_cast (show 3 ≤ x by omega)
    let z : ℤ := ((q : ℤ)-2)*x+4-y
    have hzprod : (y : ℤ)*z = ((x : ℤ)-2)^2 := by
      dsimp [z]
      linear_combination -he
    have hzpos : 0 < z := by
      by_contra hz
      have hn := mul_nonpos_of_nonneg_of_nonpos hypos.le (le_of_not_gt hz)
      rw [hzprod] at hn
      have hp : 0 < ((x : ℤ)-2)^2 := pow_pos (by omega) _
      linarith
    have hxz : z < x := by
      have hsq : ((x : ℤ)-2)^2 < (x : ℤ)*x := by linarith [show (x : ℤ) ≥ 3 from hx3]
      have hxy' : (x : ℤ) ≤ y := by exact_mod_cast hxy
      have hb := hsq.trans_le (mul_le_mul_of_nonneg_left hxy' (by positivity : (0 : ℤ) ≤ x))
      have hzle : (y : ℤ)*z < y*x := by rw [hzprod, mul_comm (y : ℤ) x]; exact hb
      exact lt_of_mul_lt_mul_left hzle hypos.le
    have hroot : ((x : ℤ)+z-2)^2 = (q : ℤ)*x*z := by
      dsimp only [z]
      linear_combination he
    let t := z.toNat
    have ht : (t : ℤ) = z := Int.toNat_of_nonneg hzpos.le
    have htz : t < x := by exact_mod_cast (show (t : ℤ) < x by rwa [ht])
    have htodd : Odd t := by
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      have hpx := congrArg (fun a : ℤ => a % 2) hzprod
      rw [← ht, Int.mul_emod, pow_two, Int.mul_emod ((x : ℤ)-2) ((x : ℤ)-2)] at hpx
      have hxx : (x : ℤ) % 2 = 1 := by exact_mod_cast (show x % 2 = 1 by omega)
      have hyy : (y : ℤ) % 2 = 1 := by exact_mod_cast (show y % 2 = 1 by omega)
      have hsub : ((x : ℤ)-2) % 2 = 1 := by omega
      rw [hyy, hsub] at hpx
      simp at hpx
      have : t % 2 = 1 := by exact_mod_cast hpx
      exact ⟨t/2, by omega⟩
    have htroot : ((t : ℤ)+x-2)^2 = (q : ℤ)*t*x := by
      rw [ht]
      linear_combination hroot
    exact (h1 (ih t htz x q htodd hx htz.le htroot).2).elim

theorem odd_components {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hd : (a+1)*(b+1) ∣ (a+b)^2) : Odd a ∧ Odd b := by
  obtain ⟨q, hq⟩ := hd
  have mixed {x y : ℕ} (hex : Even x) (hoy : Odd y)
      (he : (x+y)^2 = (x+1)*(y+1)*q) : False := by
    have ho : Odd ((x+y)^2) := (hex.add_odd hoy).pow
    obtain ⟨k, hk⟩ := hoy
    have hev : Even ((x+y)^2) := ⟨(x+1)*(k+1)*q, by
      rw [he, hk]
      ring⟩
    obtain ⟨u, hu⟩ := ho
    obtain ⟨v, hv⟩ := hev
    omega
  rcases Nat.even_or_odd a with hae | hao
  · rcases Nat.even_or_odd b with hbe | hbo
    · have hsa : Odd (a+1) := by obtain ⟨k,hk⟩ := hae; exact ⟨k, by omega⟩
      have hsb : Odd (b+1) := by obtain ⟨k,hk⟩ := hbe; exact ⟨k, by omega⟩
      have hq' : (((a+1 : ℕ) : ℤ)+(b+1 : ℕ)-2)^2 =
          (q : ℤ)*(a+1 : ℕ)*(b+1 : ℕ) := by
        push_cast
        have hqz : ((a : ℤ)+b)^2 = (a+1)*(b+1)*q := by exact_mod_cast hq
        linear_combination hqz
      have h := (odd_shifted_eq_one (a+1) (b+1) q hsa hsb (by omega) hq').1
      omega
    · exact (mixed hae hbo hq).elim
  · rcases Nat.even_or_odd b with hbe | hbo
    · exact (mixed hbe hao (by simpa only [add_comm b a, mul_comm (b+1) (a+1)] using hq)).elim
    · exact ⟨hao,hbo⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_small_y {g y z : ℕ}
    (hg : 1 < g) (hy : 3 ≤ y) (hy15 : y ≤ 15) (hgo : Odd g)
    (hyo : Odd y) (hzo : Odd z) (ho : g*y ≤ z)
    (hf : (g+1)*(y*z+1) ∣ (g+y*z)^2)
    (hh : (g*y+1)*(z+1) ∣ (g*y+z)^2) : False := by
  have largeComponent_dvd (a b : ℕ)
      (h : (a+1)*(b+1) ∣ (a+b)^2) : (b : ℤ)+1 ∣ ((a : ℤ)-1)^2 := by
    have hs : b+1 ∣ (a+b)^2 := (dvd_mul_left (b+1) (a+1)).trans h
    have hs' : (b : ℤ)+1 ∣ ((a : ℤ)+b)^2 := by exact_mod_cast hs
    have hrewrite : ((a : ℤ)-1)^2 =
        ((a : ℤ)+b)^2 - ((b : ℤ)+1)*(2*(a : ℤ)+b-1) := by ring
    rw [hrewrite]
    exact dvd_sub hs' (dvd_mul_right _ _)

  have normalized_bounds {g x y z : ℕ}
      (hg : 1 < g) (hx : 0 < x) (horder : g*y ≤ x*z)
      (hdiv : (g*x+1)*(y*z+1) ∣ (g*x+y*z)^2) :
      y*z ≤ g*x*(g*x-2) ∧ y^2 ≤ x^2*(g*x-2) := by
    have hgx : 2 ≤ g*x := by
      have := Nat.mul_le_mul_left g (show 1 ≤ x by omega)
      omega
    obtain ⟨k,hk⟩ := largeComponent_dvd (g*x) (y*z) hdiv
    push_cast at hk
    have hdpos : (0 : ℤ) < (y : ℤ)*z+1 := by positivity
    have hnpos : (0 : ℤ) < (((g : ℤ)*x)-1)^2 := by
      have hgx' : (2 : ℤ) ≤ (g : ℤ)*x := by exact_mod_cast hgx
      exact pow_pos (by omega) _
    have hkpos : 0 < k := by
      by_contra he
      have hm := mul_nonpos_of_nonneg_of_nonpos hdpos.le (le_of_not_gt he)
      rw [← hk] at hm
      exact hnpos.not_ge hm
    have hle : (y : ℤ)*z+1 ≤ (((g : ℤ)*x)-1)^2 := by
      rw [hk]
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ k by omega) hdpos.le)
    have hu : y*z ≤ g*x*(g*x-2) := by
      have hcast : ((g*x-2 : ℕ) : ℤ) = (g : ℤ)*x-2 := by
        rw [Nat.cast_sub hgx]
        push_cast
        rfl
      exact_mod_cast (show (y : ℤ)*z ≤ ((g : ℤ)*x)*((g*x-2 : ℕ) : ℤ) by
        rw [hcast]
        linarith only [hle,
          show ((g : ℤ)*x-1)^2-1 = ((g : ℤ)*x)*((g : ℤ)*x-2) by ring])
    refine ⟨hu, ?_⟩
    have ht : g*y^2 ≤ g*(x^2*(g*x-2)) := by
      calc
        g*y^2 = (g*y)*y := by ring
        _ ≤ (x*z)*y := Nat.mul_le_mul_right y horder
        _ = x*(y*z) := by ring
        _ ≤ x*(g*x*(g*x-2)) := Nat.mul_le_mul_left x hu
        _ = g*(x^2*(g*x-2)) := by ring
    exact Nat.le_of_mul_le_mul_left ht (by omega)

  have one_component_bounds {g y z : ℕ}
      (hg : 1 < g) (horder : g*y ≤ z)
      (hdiv : (g+1)*(y*z+1) ∣ (g+y*z)^2) :
      y*z ≤ g*(g-2) ∧ y^2+2 ≤ g := by
    obtain ⟨hz,hy⟩ := normalized_bounds hg (show 0 < 1 by decide)
      (by simpa using horder) (by simpa using hdiv)
    simp at hz hy
    exact ⟨hz, by omega⟩

  have difference_bounds {g x y z r s : ℤ} (hg : 2 ≤ g)
      (hx : 1 ≤ x) (hxy : x < y) (ho : g*y ≤ x*z)
      (hr : 0 < r)
      (hp : (y*z+1)*r = (g*x-1)^2)
      (hq : (x*z+1)*s = (g*y-1)^2) :
      0 < x^3*s-y^3*r ∧ x^3*s-y^3*r < 2*x^2*(y-x) := by
    have hy : 1 ≤ y := by omega
    have hgz : 0 < g*y := by positivity
    have hz : 0 < z := by
      by_contra! hn
      exact hgz.not_ge (ho.trans (mul_nonpos_of_nonneg_of_nonpos (by omega) hn))
    have hrBound : y^2*r < g*x^3 := by
      have h₁ : (g*y)*y*r ≤ (x*z)*y*r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ho (by omega)) hr.le
      have h₂ : ((x : ℤ)*(g*x-1)^2) < g*(g*x^3) := by
        have hgx : 2 ≤ g*x := by nlinarith [mul_nonneg (show 0 ≤ g-2 by omega) (show 0 ≤ x-1 by omega)]
        have hsq : (g*x-1)^2 < (g*x)^2 := by nlinarith only [hgx]
        calc
          x*(g*x-1)^2 < x*(g*x)^2 := mul_lt_mul_of_pos_left hsq (by omega)
          _ = g*(g*x^3) := by ring
      have h₃ : (x*z)*y*r ≤ x*(g*x-1)^2 := by
        calc
          (x*z)*y*r = x*(y*z*r) := by ring
          _ ≤ x*((y*z+1)*r) :=
            mul_le_mul_of_nonneg_left (by nlinarith only [hr]) (by omega)
          _ = x*(g*x-1)^2 := by rw [hp]
      have hm : g*(y^2*r) < g*(g*x^3) := by
        calc
          g*(y^2*r) = (g*y)*y*r := by ring
          _ ≤ (x*z)*y*r := h₁
          _ ≤ x*(g*x-1)^2 := h₃
          _ < g*(g*x^3) := h₂
      exact lt_of_mul_lt_mul_left hm (by omega)
    have id : (x*z+1)*(x^3*s-y^3*r) =
        (y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) := by
      linear_combination x^3*hq-y^2*x*hp
    have hCore : 0 < 2*g*x^2*y-x^2-x*y-y^2*r := by
      have hMid : x^2+x*y ≤ g*x^2*y := by
        have hxx : x ≤ x*x := by nlinarith [mul_nonneg (show 0 ≤ x by omega) (show 0 ≤ x-1 by omega)]
        have hyy : x ≤ y := by omega
        have h₁ := mul_le_mul_of_nonneg_left hyy (show 0 ≤ x by omega)
        have h₂ := mul_le_mul_of_nonneg_right hxx (show 0 ≤ y by omega)
        have h₃ : 2*(x*x*y) ≤ g*(x*x*y) :=
          mul_le_mul_of_nonneg_right hg (by positivity)
        nlinarith only [h₁,h₂,h₃]
      have hBig : g*x^3 ≤ g*x^2*y :=
        (show g*x^3 = (g*x^2)*x by ring) ▸
          mul_le_mul_of_nonneg_left hxy.le (by positivity)
      linarith only [hrBound, hMid, hBig]
    have hden : 0 < x*z+1 := by positivity
    constructor
    · by_contra! hn
      have hnon := mul_nonpos_of_nonneg_of_nonpos hden.le hn
      rw [id] at hnon
      exact (mul_pos (sub_pos.mpr hxy) hCore).not_ge hnon
    · have hLower : g*y < x*z+1 := by omega
      have hSmall : 2*g*x^2*y-x^2-x*y-y^2*r < 2*x^2*(x*z+1) := by
        have h₁ := mul_lt_mul_of_pos_left hLower (show 0 < 2*x^2 by positivity)
        have h₂ : 0 < x^2+x*y+y^2*r := by positivity
        nlinarith only [h₁,h₂]
      have hProduct :
          (x*z+1)*(x^3*s-y^3*r) < (x*z+1)*(2*x^2*(y-x)) := by
        rw [id]
        calc
          (y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) < (y-x)*(2*x^2*(x*z+1)) :=
            mul_lt_mul_of_pos_left hSmall (sub_pos.mpr hxy)
          _ = (x*z+1)*(2*x^2*(y-x)) := by ring
      exact lt_of_mul_lt_mul_left hProduct hden.le

  have component_dvd_bound {g x y z r s : ℤ}
      (hp : (y*z+1)*r = (g*x-1)^2)
      (hq : (x*z+1)*s = (g*y-1)^2)
      (hu2 : g*x+1 ∣ (y*z-1)^2) :
      let d := x^3*s-y^3*r
      let C := (x+y)*(d+(y-x)*y*(x+2*y))
      g*x+1 ∣ 16*C^2 := by
    let A := g*x+1
    let d := x^3*s-y^3*r
    let C := (x+y)*(d+(y-x)*y*(x+2*y))
    let u := y*z-1
    let K := x*d-(y-x)*y^3
    change A ∣ 16*C^2
    change A ∣ u^2 at hu2
    have hp' : A ∣ (u+2)*r-4 := ⟨g*x-3, by
      dsimp [A,u]
      linear_combination hp⟩
    have hr' : A ∣ 4*r+4*u-8 := by
      rw [show 4*r+4*u-8 = u^2*r-(u-2)*((u+2)*r-4) by ring]
      exact dvd_sub (dvd_mul_of_dvd_left hu2 r) (dvd_mul_of_dvd_right hp' (u-2))
    have hd : (x*z+1)*d = (y-x)*(2*g*x^2*y-x^2-x*y-y^2*r) := by
      dsimp [d]
      linear_combination x^3*hq-y^2*x*hp
    have hE : A ∣ d*(x*u+x+y)+(y-x)*y*(x^2+3*x*y+y^2*r) :=
      ⟨2*x*y^2*(y-x), by
        dsimp [A,u]
        linear_combination y*hd⟩
    have hLin : A ∣ 4*(C+K*u) := by
      rw [show 4*(C+K*u) =
          4*(d*(x*u+x+y)+(y-x)*y*(x^2+3*x*y+y^2*r))-
            ((y-x)*y^3)*(4*r+4*u-8) by dsimp [C,K]; ring]
      exact dvd_sub (dvd_mul_of_dvd_right hE 4)
        (dvd_mul_of_dvd_right hr' ((y-x)*y^3))
    rw [show 16*C^2 = (4*(C+K*u))*(4*(C-K*u))+(16*K^2)*u^2 by ring]
    exact dvd_add (dvd_mul_of_dvd_left hLin (4*(C-K*u)))
      (dvd_mul_of_dvd_right hu2 (16*K^2))

  let factoredProduct (fs : List (ℕ × ℕ)) : ℕ :=
    fs.foldr (fun (p,e) n => p^e*n) 1

  let factoredDivisors (fs : List (ℕ × ℕ)) : List ℕ :=
    fs.foldr (fun (p,e) ds =>
      (List.range (e+1)).flatMap fun k => ds.map fun a => p^k*a) [1]

  have mem_factoredDivisors {fs : List (ℕ × ℕ)} {a : ℕ}
      (hp : ∀ p ∈ fs, p.1.Prime) (hd : a ∣ factoredProduct fs) :
      a ∈ factoredDivisors fs := by
    induction fs generalizing a with
    | nil => simp [factoredProduct, factoredDivisors] at hd ⊢; exact hd
    | cons f fs ih =>
      obtain ⟨p,e⟩ := f
      change a ∣ p^e * factoredProduct fs at hd
      obtain ⟨b,c,hb,hc,rfl⟩ := Nat.dvd_mul.mp hd
      obtain ⟨k,hk,rfl⟩ := Nat.dvd_prime_pow (hp (p,e) (by simp)) |>.mp hb
      have hm := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hc
      change p^k*c ∈ (List.range (e+1)).flatMap (fun j =>
        (factoredDivisors fs).map fun v => p^j*v)
      exact List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega),
        List.mem_map.mpr ⟨c,hm,rfl⟩⟩

  let discriminant (y d a : ℕ) : ℤ :=
    let Y : ℤ := y
    let D : ℤ := d
    let G : ℤ := (a : ℤ)-1
    ((Y-1)*(D+Y*(Y+1)-2*G*Y^2))^2 - 4*Y^3*(Y-1)*D*(G-1)^2

  let divisorConstant (y d : ℕ) : ℕ :=
    16*((y+1)*(d+(y-1)*y*(1+2*y)))^2

  let excludesRow (y d : ℕ) (fs : List (ℕ × ℕ)) : Bool :=
    (factoredDivisors fs).all fun a =>
      let v := discriminant y d a
      decide (a % 2 ≠ 0 ∨ a < y*y+3 ∨ v.natAbs.sqrt^2 ≠ v.natAbs)

  have nonsquare_of_row {y d a : ℕ} {fs : List (ℕ × ℕ)}
      (hprod : factoredProduct fs = divisorConstant y d)
      (hprime : ∀ p ∈ fs, p.1.Prime) (hcheck : excludesRow y d fs = true)
      (hdvd : a ∣ divisorConstant y d) (he : a % 2 = 0) (hle : y*y+3 ≤ a) :
      ∀ t : ℤ, discriminant y d a ≠ t^2 := by
    intro t ht
    have hm := mem_factoredDivisors hprime (hprod ▸ hdvd : a ∣ factoredProduct fs)
    have hc := of_decide_eq_true (List.all_eq_true.mp hcheck a hm)
    rcases hc with h | h | h
    · exact h he
    · exact h.not_ge hle
    · apply h
      rw [ht, Int.natAbs_pow, Nat.sqrt_eq']

  have even_partner (a b : ℕ) (ha : Odd a) (hb : Odd b)
      (hd : (a+1)*(b+1) ∣ (a+b)^2)
      {r : ℤ} (hr : ((b : ℤ)+1)*r = ((a : ℤ)-1)^2) : ∃ j : ℤ, r = 2*j := by
    obtain ⟨q,hq⟩ := hd
    have hq' : ((a : ℤ)+b)^2 = (a+1)*(b+1)*q := by exact_mod_cast hq
    have hV : r = ((q : ℤ)-2)*(a+1)+4-(b+1) := by
      apply mul_left_cancel₀ (show ((b : ℤ)+1) ≠ 0 by positivity)
      linear_combination hr+hq'
    obtain ⟨u,hu⟩ := ha
    obtain ⟨v,hv⟩ := hb
    have hu' : (a : ℤ) = 2*(u : ℤ)+1 := by exact_mod_cast hu
    have hv' : (b : ℤ) = 2*(v : ℤ)+1 := by exact_mod_cast hv
    refine ⟨((q : ℤ)-2)*(u+1)+2-(v+1), ?_⟩
    rw [hV, hu', hv']
    ring

  have certified_rows (y d : ℕ) (hy : 3 ≤ y) (hy15 : y ≤ 15) (hyo : y % 2 = 1)
      (hd : 0 < d) (hdhi : d < 2*(y-1)) (hde : d % 2 = 0) :
      ∃ fs : List (ℕ × ℕ), factoredProduct fs = divisorConstant y d ∧
        (∀ p ∈ fs, p.1.Prime) ∧ excludesRow y d fs = true := by
    interval_cases y <;> interval_cases d <;> first | omega | skip
    · refine ⟨[(2, 12), (11, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (3, 4), (37, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 16), (3, 2), (7, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (3, 2), (113, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 16), (79, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 12), (317, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 14), (3, 2), (53, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 12), (11, 2), (29, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 24), (5, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (5, 4), (137, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 10), (5, 2), (7, 6)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (3, 2), (5, 2), (229, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 16), (5, 2), (43, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (5, 2), (13, 2), (53, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 10), (3, 2), (5, 4), (23, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (5, 2), (691, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 12), (3, 4), (211, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 10), (3, 2), (7, 2), (181, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 14), (3, 2), (317, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 10), (3, 8), (47, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 12), (3, 2), (5, 2), (127, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 10), (3, 2), (31, 2), (41, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 16), (3, 4), (53, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 10), (3, 2), (19, 2), (67, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 12), (3, 2), (7, 4), (13, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (7, 6), (43, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 12), (7, 2), (17, 2), (31, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (3, 2), (7, 2), (19, 2), (37, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 10), (5, 2), (7, 2), (211, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (7, 2), (2111, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 20), (3, 2), (7, 2), (11, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (7, 2), (2113, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 10), (7, 4), (151, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (3, 4), (5, 2), (7, 2), (47, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 12), (7, 2), (23, 4)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 8), (7, 2), (29, 2), (73, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 20), (11, 2), (37, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 14), (3257, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 16), (3, 4), (181, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 14), (3259, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 18), (5, 2), (163, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 14), (3, 2), (1087, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 16), (7, 2), (233, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 14), (13, 2), (251, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 26), (3, 2), (17, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 14), (5, 2), (653, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 16), (23, 2), (71, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 14), (3, 6), (11, 4)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
    · refine ⟨[(2, 18), (19, 2), (43, 2)], by decide, ?_, by decide +kernel⟩
      simp [List.mem_cons]
      try norm_num
  obtain ⟨_, hybound⟩ := one_component_bounds hg ho hf
  obtain ⟨r, hr'⟩ := largeComponent_dvd g (y*z) hf
  obtain ⟨s, hs'⟩ := largeComponent_dvd (g*y) z hh
  have hr := hr'.symm
  have hs := hs'.symm
  have hrpos : 0 < r := by
    have hden : 0 < (((y*z : ℕ) : ℤ)+1) := by positivity
    have hn : 0 < ((g : ℤ)-1)^2 := by
      have hg' : (1 : ℤ) < g := by exact_mod_cast hg
      exact pow_pos (sub_pos.mpr hg') _
    by_contra! hle
    exact hn.not_ge (hr ▸ mul_nonpos_of_nonneg_of_nonpos hden.le hle)
  obtain ⟨u,hu⟩ := even_partner g (y*z) hgo (hyo.mul hzo) hf hr
  obtain ⟨v,hv⟩ := even_partner (g*y) z (hgo.mul hyo) hzo hh hs
  push_cast at hr hs
  have ho' : (g : ℤ)*y ≤ z := by exact_mod_cast ho
  have hg' : (2 : ℤ) ≤ g := by exact_mod_cast (show 2 ≤ g by omega)
  have hy' : (1 : ℤ) < y := by exact_mod_cast (show 1 < y by omega)
  let d := s-(y : ℤ)^3*r
  have hd : (0 : ℤ) < d ∧ d < 2*((y : ℤ)-1) := by
    simpa [d] using difference_bounds (g := (g : ℤ)) (x := 1)
      hg' (by decide) hy' (by simpa using ho') hrpos (by simpa using hr)
      (by simpa using hs)
  let D := d.toNat
  have hD : (D : ℤ) = d := Int.toNat_of_nonneg hd.1.le
  have hDb : 0 < D ∧ D < 2*(y-1) := by
    have hy0 : 1 ≤ y := by omega
    have hd' : (0 : ℤ) < D ∧ (D : ℤ) < 2*(((y-1 : ℕ) : ℤ)) := by
      rw [hD, Nat.cast_sub hy0]
      simpa using hd
    exact_mod_cast hd'
  have hDe : D % 2 = 0 := by
    have hf : d = 2*(v-(y : ℤ)^3*u) := by
      dsimp [d]
      rw [hu,hv]
      ring
    omega
  have hyo' : y % 2 = 1 := by obtain ⟨k,hk⟩ := hyo; omega
  have hgo' : (g+1) % 2 = 0 := by obtain ⟨k,hk⟩ := hgo; omega
  have hdvs : (g : ℤ)+1 ∣ ((y : ℤ)*z-1)^2 := by
    have hv := largeComponent_dvd (y*z) g (by simpa [mul_comm, add_comm] using hf)
    push_cast at hv
    exact hv
  have hmain := component_dvd_bound (x := 1) (by simpa using hr)
    (by simpa using hs) (by simpa using hdvs)
  have hconstant : g+1 ∣ divisorConstant y D := by
    apply Int.natCast_dvd_natCast.mp
    have hy0 : 1 ≤ y := by omega
    simp only [divisorConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_sub hy0, Nat.cast_one, hD]
    simpa [d, add_comm 1 (y : ℤ)] using hmain
  obtain ⟨fs,hprod,hprime,hrow⟩ := certified_rows y D hy hy15 hyo' hDb.1 hDb.2 hDe
  have hsize : y*y+3 ≤ g+1 := by simpa [pow_two] using Nat.succ_le_succ hybound
  have hdiscr := nonsquare_of_row hprod hprime hrow hconstant hgo' hsize
  have hdelta : ((z : ℤ)+1)*d =
      ((y : ℤ)-1)*(2*(g : ℤ)*y-y-1-(y : ℤ)^2*r) := by
    dsimp [d]
    linear_combination hs - (y : ℤ)^2*hr
  have hquad : d*(((g : ℤ)-1)^2+((y : ℤ)-1)*r) =
      (y : ℤ)*r*((y : ℤ)-1)*(2*(g : ℤ)*y-y-1-(y : ℤ)^2*r) := by
    rw [show ((g : ℤ)-1)^2+((y : ℤ)-1)*r = y*r*(z+1) by linear_combination -hr]
    linear_combination ((y : ℤ)*r)*hdelta
  let A : ℤ := (y : ℤ)^3*((y : ℤ)-1)
  let B : ℤ := ((y : ℤ)-1)*(d+(y : ℤ)*(y+1)-2*(g : ℤ)*y^2)
  apply hdiscr (2*A*r+B)
  dsimp [discriminant,A,B]
  rw [hD]
  linear_combination (-4*(y : ℤ)^3*((y : ℤ)-1))*hquad

/-- The smaller coprime component is one. -/
def H1 : Prop :=
  ∀ g y z : ℕ, 1 < g → 17 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    (g*y+1)*(z+1) ∣ (g*y+z)^2 → g = z

/-- Both coprime components are nontrivial, in increasing order. -/
def H2 : Prop :=
  ∀ g x y z : ℕ, 1 < g → 3 ≤ x → x < y →
    Odd g → Odd x → Odd y → Odd z → g*y ≤ x*z → Nat.Coprime x y →
    (g*x+1)*(y*z+1) ∣ (g*x+y*z)^2 →
    (g*y+1)*(x*z+1) ∣ (g*y+x*z)^2 → g = z

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1.H2 := by
  intro hone hlarge g x y z hg hx hy hz hne hsort₁ hsort₂ hcop hdiv₁ hdiv₂
  have go : ∀ x y : ℕ, 0 < x → 0 < y → x < y →
      g*x ≤ y*z → g*y ≤ x*z → Nat.Coprime x y →
      (g*x+1)*(y*z+1) ∣ (g*x+y*z)^2 →
      (g*y+1)*(x*z+1) ∣ (g*y+x*z)^2 → g = z := by
    intro u v hu hv huv h₁ h₂ cop du dv
    have odd₁ := odd_components (mul_pos (by omega : 0 < g) hu) h₁ du
    have odd₂ := odd_components (mul_pos (by omega : 0 < g) hv) h₂ dv
    have og := Nat.Odd.of_mul_left odd₁.1
    have ou := Nat.Odd.of_mul_right odd₁.1
    have ov := Nat.Odd.of_mul_right odd₂.1
    have oz := Nat.Odd.of_mul_right odd₁.2
    by_cases huone : u = 1
    · subst u
      have hvthree : 3 ≤ v := by obtain ⟨k,hk⟩ := ov; omega
      have horder : g*v ≤ z := by simpa using h₂
      have hf : (g+1)*(v*z+1) ∣ (g+v*z)^2 := by simpa using du
      have hh : (g*v+1)*(z+1) ∣ (g*v+z)^2 := by simpa using dv
      by_cases hv15 : v ≤ 15
      · exact (no_small_y hg hvthree hv15 og ov oz horder hf hh).elim
      have hv17 : 17 ≤ v := by obtain ⟨k,hk⟩ := ov; omega
      exact hone g v z hg hv17 og ov oz horder hf hh
    · have huthree : 3 ≤ u := by obtain ⟨k,hk⟩ := ou; omega
      exact hlarge g u v z hg huthree huv og ou ov oz h₂ cop du dv
  rcases lt_or_gt_of_ne hne with h | h
  · exact go x y hx hy h hsort₁ hsort₂ hcop hdiv₁ hdiv₂
  · exact go y x hy hx h hsort₂ hsort₁ hcop.symm hdiv₂ hdiv₁

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1
