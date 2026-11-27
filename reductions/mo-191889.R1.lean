import OMAStatements.S_mo_191889
import Mathlib

/-!
# Powerful sums of coprime fourth powers

Elkies and Goel, *On powerful integers expressible as sums of two coprime
fourth powers*, sections 3 and 4, https://antsmath.org/ANTSXV/papers/ANTS-XV_elkies-goel.pdf.

We verify the proposed minimum is attained. Every smaller candidate has
the form b*z^2 with b squarefree, b dividing z, and all prime factors of b
congruent to 1 modulo 8. Fermat's theorem excludes b = 1. The remaining
searches follow the small, exceptional and large parameter cases in the paper.
-/

namespace OMA.R_mo_191889_R1

open OMA.S_mo_191889

def H1 : Prop :=
  ∀ b z x y : ℕ, 1 < b → b ≤ 10000 → b ∉ ({4721, 4777, 6497, 6577, 9881} : Finset ℕ) →
    Squarefree b → (∀ p ∈ b.primeFactors, p % 8 = 1) → b ∣ z →
    0 < x → x ≤ y → y ≤ 1325648472 → x.Coprime y →
    x^4 + y^4 = b*z^2 → b*z^2 < 3088257489493360278725196965477359217 → False

def H2 : Prop :=
  ∀ b z x y : ℕ, b ∈ ({4721, 4777, 6497, 6577, 9881} : Finset ℕ) →
    Squarefree b → (∀ p ∈ b.primeFactors, p % 8 = 1) → b ∣ z →
    0 < x → x ≤ y → y ≤ 1325648472 → x.Coprime y →
    x^4 + y^4 = b*z^2 → b*z^2 < 3088257489493360278725196965477359217 → False

def H3 : Prop :=
  ∀ b z x y : ℕ, 10000 < b → b ≤ 1456256357804 →
    Squarefree b → (∀ p ∈ b.primeFactors, p % 8 = 1) → b ∣ z →
    0 < x → x ≤ y → y ≤ 1325648472 → x.Coprime y →
    x^4 + y^4 = b*z^2 → b*z^2 < 3088257489493360278725196965477359217 → False

section Arithmetic

private theorem not_four {x y : ℕ} (hc : x.Coprime y) : ¬ 4 ∣ x^4+y^4 := by
  intro h
  have tab : ∀ i j : Fin 4, (i.val^4+j.val^4)%4 = 0 →
      i.val%2 = 0 ∧ j.val%2 = 0 := by decide
  have congr := ((Nat.mod_modEq x 4).pow 4).add ((Nat.mod_modEq y 4).pow 4)
  have h0 : ((x%4)^4+(y%4)^4)%4 = 0 := congr.trans h.modEq_zero_nat
  obtain ⟨hx,hy⟩ := tab ⟨x%4, Nat.mod_lt _ (by decide)⟩ ⟨y%4, Nat.mod_lt _ (by decide)⟩ h0
  change (x%4)%2 = 0 at hx
  change (y%4)%2 = 0 at hy
  rw [Nat.mod_mod_of_dvd x (by decide : 2 ∣ 4)] at hx
  rw [Nat.mod_mod_of_dvd y (by decide : 2 ∣ 4)] at hy
  have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hx) (Nat.dvd_of_mod_eq_zero hy)
  rw [show x.gcd y = 1 from hc] at hd
  norm_num at hd

private theorem prime_residue {x y p : ℕ} (hc : x.Coprime y) (hp : p.Prime)
    (hne : p ≠ 2) (hd : p ∣ x^4+y^4) : p%8 = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff (x^4+y^4) p).mpr hd
  push_cast at hz
  have hy : (y : ZMod p) ≠ 0 := by
    intro hy
    have hx : (x : ZMod p) = 0 := by simpa [hy] using hz
    have gd := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff x p).mp hx)
      ((ZMod.natCast_eq_zero_iff y p).mp hy)
    rw [show x.gcd y = 1 from hc] at gd
    exact hp.not_dvd_one gd
  let u := (x : ZMod p) / y
  have hu4 : u^4 = -1 := by
    change ((x : ZMod p) / y)^4 = -1
    rw [div_pow,div_eq_iff (pow_ne_zero _ hy)]
    linear_combination hz
  have hu8 : u^8 = 1 := by rw [show 8 = 4*2 by decide,pow_mul,hu4]; norm_num
  have hnot : u^4 ≠ 1 := by
    rw [hu4]
    intro he
    have htwo : (2 : ZMod p) = 0 := by linear_combination -he
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 p).mp htwo)
    have := hp.two_le
    omega
  have hd8 := orderOf_dvd_of_pow_eq_one hu8
  have hd4 : ¬ orderOf u ∣ 4 := fun h => hnot (orderOf_dvd_iff_pow_eq_one.mp h)
  have order : orderOf u = 8 := by
    have le := Nat.le_of_dvd (by decide : 0 < 8) hd8
    generalize hh : orderOf u = m at *
    interval_cases m <;> norm_num at *
  have une : u ≠ 0 := by intro h; simp [h] at hu8
  have div := ZMod.orderOf_dvd_card_sub_one une
  rw [order] at div
  obtain ⟨j,hj⟩ := div
  have := hp.two_le
  omega

private theorem kernel_dvd {b z : ℕ} (hb : Squarefree b) (hz : 0 < z)
    (hpw : IsPowerful (z^2*b)) : b ∣ z := by
  rw [← Nat.prod_primeFactors_of_squarefree hb, Nat.prod_primeFactors_dvd_iff hz.ne']
  intro p hp
  obtain ⟨hprime,hpb,_⟩ := Nat.mem_primeFactors.mp hp
  refine Nat.mem_primeFactors.mpr ⟨hprime,?_,hz.ne'⟩
  by_contra hn
  have cop := ((hprime.coprime_iff_not_dvd.mpr hn).pow_left 2).pow_right 2
  have h2 := hpw.2 p hprime (dvd_mul_of_dvd_right hpb _)
  have bad := cop.dvd_of_dvd_mul_left h2
  exact Nat.squarefree_iff_prime_squarefree.mp hb p hprime (by simpa [pow_two] using bad)

private theorem attained : IsPowerful 3088257489493360278725196965477359217 ∧
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x.Coprime y ∧ 3088257489493360278725196965477359217 = x^4+y^4 := by
  refine ⟨⟨by decide,?_⟩,427511122,1322049209,by decide,by decide,by decide,by decide⟩
  let z : ℕ := 17*73993169*338837713
  have h : 3088257489493360278725196965477359217 = 17*z^2 := by decide
  rw [h]
  intro p hp hd
  have hz : p ∣ z := (hp.dvd_mul.mp hd).elim (fun h => h.trans (by decide : 17 ∣ z)) hp.dvd_of_dvd_pow
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hz 2) _

end Arithmetic

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_191889.main := by
  intro small exceptional large
  refine ⟨attained,?_⟩
  rintro n ⟨hpow,x,y,hx,hy,hcop,heq⟩
  by_contra! hn
  obtain ⟨b,z,hb,hz,hfact,hsq⟩ := Nat.sq_mul_squarefree_of_pos hpow.1
  have hd := kernel_dvd hsq hz (hfact.symm ▸ hpow)
  have eq : x^4+y^4 = b*z^2 := by rw [← heq,← hfact,mul_comm]
  have hn' : b*z^2 < 3088257489493360278725196965477359217 := by simpa only [mul_comm b _,hfact] using hn
  have bNe : b ≠ 1 := by
    intro h
    rw [h,one_mul] at eq
    exact not_fermat_42 (a := (x:ℤ)) (b := (y:ℤ)) (c := (z:ℤ))
      (by exact_mod_cast hx.ne') (by exact_mod_cast hy.ne') (by exact_mod_cast eq)
  have hres (p : ℕ) (hp : p ∈ b.primeFactors) : p%8=1 := by
    obtain ⟨hpr,hpb,_⟩ := Nat.mem_primeFactors.mp hp
    have hpn : p ∣ n := hfact ▸ dvd_mul_of_dvd_right hpb _
    apply prime_residue hcop hpr _ (heq ▸ hpn)
    intro hp2
    subst p
    exact not_four hcop (heq ▸ hpow.2 2 Nat.prime_two hpn)
  have hbz := Nat.le_of_dvd hz hd
  have hlim : b^3 ≤ b*z^2 := by
    rw [show b^3 = b*b^2 by ring]
    gcongr
  have bmax : b ≤ 1456256357804 := by
    by_contra! h
    have ge := Nat.pow_le_pow_left (show 1456256357805 ≤ b by omega) 3
    omega
  have exclude (u v : ℕ) (hu : 0 < u) (huv : u ≤ v) (hc : u.Coprime v)
      (he : u^4+v^4 = b*z^2) : False := by
    have vmax : v ≤ 1325648472 := by
      by_contra! h
      have ge := Nat.pow_le_pow_left (show 1325648473 ≤ v by omega) 4
      omega
    by_cases exc : b ∈ ({4721, 4777, 6497, 6577, 9881} : Finset ℕ)
    · exact exceptional b z u v exc hsq hres hd hu huv vmax hc he hn'
    by_cases lo : b ≤ 10000
    · exact small b z u v (by omega) lo exc hsq hres hd hu huv vmax hc he hn'
    · exact large b z u v (by omega) bmax hsq hres hd hu huv vmax hc he hn'
  rcases le_total x y with h | h
  · exact exclude x y hx h hcop eq
  · exact exclude y x hy h hcop.symm (by simpa [add_comm] using eq)

end OMA.R_mo_191889_R1

