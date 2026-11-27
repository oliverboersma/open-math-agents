import OMAReductions.R_OeisA224_conjecture_R1_H2_R1
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-! A finite search over the last prime power for each complementary factor.
The prime-power count through the cleared identity is from HudZah's merged
reduction #1064. The first local divisibility condition appears in section 6 of
umaia1234/agentic-conjectures, OEIS A000224. The second modulus and the bounds
for the removed prime power are derived below. -/

open Finset OeisA224
namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R2

theorem count_step (p e : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    a (p^(e+2)) = a (p^e) + (p^(e+1)*(p-1))/2 := by
  classical
  let residues (n : ℕ) : Finset ℕ :=
    (Finset.range n).image (fun k => k^2 % n)

  have mem_res {n r : ℕ} (hn : 0 < n) :
      r ∈ residues n ↔ ∃ k : ℕ, k^2 % n = r := by
    constructor
    · intro hr
      obtain ⟨k, _, h⟩ := Finset.mem_image.mp hr
      exact ⟨k, h⟩
    · rintro ⟨k, rfl⟩
      exact Finset.mem_image.mpr ⟨k % n, Finset.mem_range.mpr (Nat.mod_lt _ hn), (Nat.pow_mod ..).symm⟩

  let unitSq (n : ℕ) [NeZero n] : Finset ℕ := by
    classical
    exact Finset.univ.image (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
      (u.val.val).val)

  have mem_unitSq {n x : ℕ} [NeZero n] :
      x ∈ unitSq n ↔ ∃ u : (ZMod n)ˣ, ((u : ZMod n)^2).val = x := by
    classical
    constructor
    · intro hx
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv⟩ := u.property
      exact ⟨v, by simpa [← hv] using hu⟩
    · rintro ⟨u, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨u ^ 2, u, rfl⟩, Finset.mem_univ _, rfl⟩

  have unitSq_card (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] (hn : 2 < n) :
      (unitSq n).card = n.totient / 2 := by
    classical
    unfold unitSq
    have hi : Function.Injective (fun u : (powMonoidHom 2 : (ZMod n)ˣ →* (ZMod n)ˣ).range =>
        u.val.val.val) := fun _ _ h => Subtype.ext (Units.ext (ZMod.val_injective n h))
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.gcd_eq_right (even_iff_two_dvd.mp (Nat.totient_even hn))]

  let N := p^(e+2)
  have hp0 := hp.pos
  have hn0 : 0 < N := pow_pos hp0 _
  have : NeZero N := ⟨hn0.ne'⟩
  have : IsCyclic (ZMod N)ˣ := ZMod.isCyclic_units_of_prime_pow p hp hne (e+2)
  have fact (u : ℕ) : (p*u)^2 % N = p^2 * (u^2 % p^e) := by
    rw [show N = p^2*p^e by dsimp [N]; ring, mul_pow, Nat.mul_mod_mul_left]
  let M := (residues (p^e)).image (fun t => p^2*t)
  have split : residues N = M ∪ unitSq N := by
    ext r
    constructor
    · intro hr
      obtain ⟨k, rfl⟩ := (mem_res hn0).mp hr
      by_cases hpk : p ∣ k
      · obtain ⟨u, rfl⟩ := hpk
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨u^2 % p^e, (mem_res (pow_pos hp0 _)).mpr ⟨u, rfl⟩, (fact u).symm⟩)
      · have hu : IsUnit (k : ZMod N) := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr hpk
        apply Finset.mem_union_right
        apply mem_unitSq.mpr
        exact ⟨hu.unit, by rw [IsUnit.unit_spec, ← Nat.cast_pow, ZMod.val_natCast]⟩
    · intro hr
      rcases Finset.mem_union.mp hr with hr | hr
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨u, rfl⟩ := (mem_res (pow_pos hp0 _)).mp ht
        exact (mem_res hn0).mpr ⟨p*u, fact u⟩
      · obtain ⟨u, rfl⟩ := mem_unitSq.mp hr
        exact (mem_res hn0).mpr ⟨u.val.val, by rw [← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]⟩
  have disj : Disjoint M (unitSq N) := by
    apply Finset.disjoint_left.mpr
    rintro r hr hunit
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, hu⟩ := mem_unitSq.mp hunit
    have hU : IsUnit (((p^2*t : ℕ) : ZMod N)) := by
      rw [← hu, ZMod.natCast_zmod_val]
      exact u.isUnit.pow 2
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (show 0 < e+2 by omega)).mp hU
      ((dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _))
  have high : 2 < N := lt_of_lt_of_le (lt_of_le_of_ne hp.two_le (Ne.symm hne))
    (Nat.le_pow (by omega : 0 < e+2))
  have hcnt : (unitSq N).card = _ := unitSq_card N high
  have hcard : (residues (p^e)).card = a (p^e) := by rw [a, if_neg (pow_ne_zero _ hp.ne_zero)]
  change a N = _
  rw [a, if_neg hn0.ne']
  change (residues N).card = _
  rw [split, Finset.card_union_of_disjoint disj, hcnt]
  dsimp only [M]
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h), hcard]
  dsimp only [N]
  rw [Nat.totient_prime_pow_succ hp]

private theorem prime_count {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) : a p = p / 2 + 1 := by
  rw [OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp hodd]
  have := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  omega

theorem count_formula (p : ℕ) (hp : p.Prime) (po : Odd p) (e : ℕ) :
    2*(p+1)*(a (p^e)-1) + (if Even e then p else 1) = p^(e+1) := by
  have hne : p ≠ 2 := by rintro rfl; norm_num at po
  induction e using Nat.twoStepInduction with
  | zero => simp [a_1]
  | one =>
    simp only [pow_one, prime_count hp hne, Nat.add_sub_cancel]
    obtain ⟨k, hk⟩ := po
    have hhalf : p/2 = k := by omega
    rw [hhalf, hk]
    simp
    ring
  | more e ih _ =>
    let x := p^(e+1)
    let q := x*(p-1)/2
    have hdouble : 2*q = x*(p-1) := by
      apply Nat.mul_div_cancel'
      apply dvd_mul_of_dvd_right
      have hh := Nat.odd_iff.mp po
      omega
    have ha : 1 ≤ a (p^e) := by
      rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
      exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
    have hadd : a (p^(e+2)) - 1 = (a (p^e) - 1) + q := by
      rw [count_step p e hp hne]
      change a (p^e) + q - 1 = _
      omega
    have ev : Even (e+2) ↔ Even e := by simp only [Nat.even_iff]; omega
    rw [hadd, if_congr ev rfl rfl]
    calc
      _ = (2*(p+1)*(a (p^e)-1) + (if Even e then p else 1)) + (p+1)*(2*q) := by ring
      _ = x + (p+1)*(x*(p-1)) := by rw [ih, hdouble]
      _ = p^((e+2)+1) := by
        rw [show e+2+1 = (e+1)+2 by omega, pow_add]
        change x + (p+1)*(x*(p-1)) = x*p^2
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
        rw [hj]
        simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
        ring

theorem cleared (p e : ℕ) (hp : p.Prime) (hpo : Odd p) :
    2*(p+1)*a (p^e) = p*p^e + (if Even e then p+2 else 2*p+1) := by
  have h := count_formula p hp hpo e
  have ha : 1 ≤ a (p^e) := by
    rw [a, if_neg (pow_ne_zero _ hp.ne_zero), Finset.one_le_card]
    exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (pow_pos hp.pos e), by simp⟩⟩
  have restore := congrArg (fun x => 2*(p+1)*x) (Nat.sub_add_cancel ha)
  by_cases hEven : Even e <;> simp only [hEven, if_true, if_false, pow_succ] at * <;> nlinarith only [h, restore]


/-- Eliminate the chosen prime power separately modulo the square count and its predecessor. -/
private theorem two_residues {m p x r A c g : ℕ}
    (hAr : 0 < A*r) (hcount : g*r = p*x+c)
    (ht : (m*x)^2 ≡ 1 [MOD (A*r)*(A*r-1)]) :
    (m*c)^2 ≡ p^2 [MOD r] ∧
    ((m : ZMod (A*r-1)) * (g - A*c))^2 = ((p : ZMod (A*r-1))*A)^2 := by
  have h1 := ht.of_dvd (show r ∣ (A*r)*(A*r-1) from
    (dvd_mul_left r A).trans (dvd_mul_right _ _))
  have h2 := ht.of_dvd (dvd_mul_left (A*r-1) (A*r))
  constructor
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    have he := congrArg (fun k : ℕ => (k : ZMod r)) hcount
    push_cast at he hz ⊢
    rw [ZMod.natCast_self, mul_zero] at he
    have hc : (c : ZMod r) = -(p*x) := by linear_combination -he
    rw [hc]
    linear_combination (p : ZMod r)^2 * hz
  · let s := A*r-1
    have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    have he := congrArg (fun k : ℕ => (k : ZMod s)) hcount
    have hrep := congrArg (fun k : ℕ => (k : ZMod s)) (Nat.sub_add_cancel (show 1 ≤ A*r by omega))
    change ((s+1 : ℕ) : ZMod s) = ((A*r : ℕ) : ZMod s) at hrep
    push_cast at he hz hrep
    rw [ZMod.natCast_self, zero_add] at hrep
    change ((m : ZMod s)*(g-A*c))^2 = (p*A)^2
    have hc : (g : ZMod s)-A*c = A*p*x := by
      linear_combination (A : ZMod s)*he + (g : ZMod s)*hrep
    rw [hc]
    linear_combination ((p : ZMod s)*A)^2 * hz

/-- For exponent two the quadratic relation for the square count reduces
the congruence to a positive linear expression in p. -/
private theorem square_bound {p m r : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m)
    (hcount : 2*(p+1)*r = p*p^2+(p+2))
    (hres : (m*(p+2))^2 ≡ p^2 [MOD r]) : p ≤ 27*m^2 := by
  have he : 2*r+p = p^2+2 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < p+1 by omega)
    nlinarith only [hcount]
  have hlin : (5*p+2)*m^2+2 ≡ p [MOD r] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hres
    have h := congrArg (fun k : ℕ => (k : ZMod r)) he
    push_cast at h hz ⊢
    rw [ZMod.natCast_self, mul_zero, zero_add] at h
    linear_combination hz + ((m : ZMod r)^2-1)*h
  have hpos : p < (5*p+2)*m^2+2 := by
    have hx : 0 < m^2 := by positivity
    nlinarith [Nat.le_mul_of_pos_right p hx]
  have hd := (Nat.modEq_iff_dvd' hpos.le).mp hlin.symm
  have hr := Nat.le_of_dvd (Nat.sub_pos_of_lt hpos) hd
  have hb : p^2 ≤ (27*m^2)*p := by
    have hx : 1 ≤ m^2 := Nat.succ_le_of_lt (by positivity)
    have hh : 2 ≤ p*m^2 := by nlinarith [Nat.mul_le_mul_right (m^2) hp]
    have hh' : 2*m^2 ≤ p*m^2 := Nat.mul_le_mul_right _ hp
    have hr0 : r ≤ (5*p+2)*m^2+2 := hr.trans (Nat.sub_le _ _)
    nlinarith only [he,hr0,hh,hh',Nat.zero_le (p*m^2)]
  exact Nat.le_of_mul_le_mul_right (by simpa [pow_two] using hb) (by omega)

/-- A bounded last prime power is enough, whatever its exponent. -/
private theorem power_bound {p e m r : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m) (he : 2 ≤ e)
    (hc : 2*(p+1)*r = p*p^e + (if Even e then p+2 else 2*p+1))
    (hres : (m*(if Even e then p+2 else 2*p+1))^2 ≡ p^2 [MOD r]) :
    p^e ≤ (27*m^2)^3 := by
  let c := if Even e then p+2 else 2*p+1
  have hc1 : p < c := by dsimp [c]; split <;> omega
  have hc2 : c ≤ 3*p := by dsimp [c]; split <;> omega
  have hp0 : 0 < p := by omega
  have hm0 : 0 < m := by omega
  have hsize : p^e ≤ 3*r := by
    apply Nat.le_of_mul_le_mul_left (c := p) _ hp0
    calc p*p^e ≤ 2*(p+1)*r := by omega
         _ ≤ p*(3*r) := by nlinarith only [Nat.mul_le_mul_right r hp]
  by_cases htwo : e = 2
  · subst e
    norm_num at hc hres
    have h := square_bound hp hm hc hres
    calc p^2 ≤ (27*m^2)^2 := Nat.pow_le_pow_left h _
         _ ≤ (27*m^2)^3 := Nat.pow_le_pow_right (by positivity) (by decide)
  · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 2 ≤ e by omega)
    have hkpos : 0 < k := by omega
    have hxp : p < m*c := by nlinarith [Nat.le_mul_of_pos_left c hm0]
    have hxp2 : p^2 < (m*c)^2 := Nat.pow_lt_pow_left hxp (by decide)
    have hr := Nat.le_of_dvd (Nat.sub_pos_of_lt hxp2) ((Nat.modEq_iff_dvd' hxp2.le).mp hres.symm)
    have hr' : r ≤ (m*c)^2 := by omega
    have hcub : p^e ≤ (27*m^2)*p^2 := by
      calc p^e ≤ 3*(m*c)^2 := hsize.trans (Nat.mul_le_mul_left 3 hr')
           _ ≤ 3*(m*(3*p))^2 := Nat.mul_le_mul_left 3
              (Nat.pow_le_pow_left (Nat.mul_le_mul_left m hc2) _)
           _ = _ := by ring
    have heq : p^e = p^k*p^2 := by rw [hk, pow_add, mul_comm]
    rw [heq] at hcub ⊢
    have hkbound := Nat.le_of_mul_le_mul_right hcub (pow_pos hp0 2)
    have hpbound := (Nat.le_pow hkpos : p ≤ p^k).trans hkbound
    calc p^k*p^2 ≤ (27*m^2)*(27*m^2)^2 := Nat.mul_le_mul hkbound (Nat.pow_le_pow_left hpbound _)
         _ = _ := by ring

/-- An exponent-one factor is reconstructed from a divisor of the smaller cofactor's square minus one.
The first congruence is divided by that known divisor before the final test. -/
def H1 : Prop := ∀ m d : ℕ, Odd m → 2 ≤ m.primeFactors.card → d ∈ (m^2-1).divisors →
  (2*d-1).Prime → m.Coprime (2*d-1) → (∀ q ∈ m.primeFactors, q ≤ 2*d-1) →
  a m ∣ (m^2-1)/d + 4*m^2*(d-1) →
  ((m : ZMod (a m*d-1))*(2-(a m : ZMod (a m*d-1))))^2 ≠ (a m : ZMod (a m*d-1))^2

/-- Higher powers are bounded in terms of m alone. Both residual tests eliminate
the prime power from their right-hand polynomials. -/
def H2 : Prop := ∀ m p e : ℕ, Odd m → 2 ≤ m.primeFactors.card → p.Prime → Odd p →
  m.Coprime p → (∀ q ∈ m.primeFactors, q ≤ p) → 2 ≤ e → p^e ≤ (27*m^2)^3 →
  let A := a m
  let r := a (p^e)
  let c := if Even e then p+2 else 2*p+1
  p.Coprime (A*r-1) → (m*c)^2 ≡ p^2 [MOD r] → A*r ∣ (m*p^e)^2-1 →
  ((m : ZMod (A*r-1))*(2*(p+1)-A*c))^2 ≠ ((p : ZMod (A*r-1))*A)^2

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1_H2_R1.H2 := by
  intro hone hhigher n ho hnum ht
  have hn : n ≠ 0 := by rintro rfl; simp at hnum
  have hnon : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  let p := n.primeFactors.max' hnon
  have hmem : p ∈ n.primeFactors := Finset.max'_mem _ _
  have hp := Nat.prime_of_mem_primeFactors hmem
  have hpodd : Odd p := by
    by_contra h
    exact ho.not_two_dvd_nat ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h)).trans
      (Nat.dvd_of_mem_primeFactors hmem))
  let e := n.factorization p
  let m := n / p^e
  have he : 0 < e := hp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hmem)
  have hm : 0 < m := Nat.ordCompl_pos p hn
  have hnrep : m*p^e=n := (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self n p)
  have hcp : m.Coprime p := (Nat.coprime_ordCompl hp hn).symm
  have hmfac : m.primeFactors ⊆ n.primeFactors := by
    rw [← hnrep, Nat.primeFactors_mul hm.ne' (pow_ne_zero _ hp.ne_zero)]
    exact Finset.subset_union_left
  have hmax : ∀ q ∈ m.primeFactors, q ≤ p :=
    fun q hq => Finset.le_max' _ _ (hmfac hq)
  have hmc : 2 ≤ m.primeFactors.card := by
    have h := hnum
    rw [← hnrep, Nat.primeFactors_mul hm.ne' (pow_ne_zero _ hp.ne_zero),
      Nat.primeFactors_prime_pow he.ne' hp] at h
    have hle := Finset.card_union_le m.primeFactors {p}
    simp only [Finset.card_singleton] at hle
    omega
  have hm2 : 2 ≤ m := by
    by_contra! h
    interval_cases m <;> simp_all
  have hmo : Odd m := by
    have h : Odd (m*p^e) := hnrep ▸ ho
    exact (Nat.odd_mul.mp h).1
  have ha := OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime hm (pow_pos hp.pos e)
    (hcp.pow_right e)
  rw [← hnrep, ha] at ht
  have hA := OMA.R_OeisA224_conjecture_R1.two_le_a m hm2
  have hpe : 2 ≤ p^e := hp.two_le.trans (Nat.le_pow he)
  have hr := OMA.R_OeisA224_conjecture_R1.two_le_a (p^e) hpe
  have hpos : 0 < a m*a (p^e) := Nat.mul_pos (by omega) (by omega)
  have hdvd : a m*a (p^e) ∣ (m*p^e)^2-1 :=
    (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt (by positivity))).mp (ht.of_dvd (dvd_mul_right _ _)).symm
  by_cases he1 : e=1
  · rw [he1, pow_one] at ht hdvd hpos
    let d := a p
    have h2p : p ≠ 2 := by intro h; rw [h] at hpodd; norm_num at hpodd
    have hdouble : 2*d = p+1 := by
      dsimp only [d]
      rw [OMA.R_OeisA224_conjecture_R1.card_squares_prime p hp h2p]
      obtain ⟨i, hi⟩ := hpodd
      omega
    have hpval : 2*d-1 = p := by omega
    have ⟨hloc,hlast⟩ := two_residues (p:=1) (x:=p) (c:=1) (g:=2) hpos
      (by simpa only [one_mul] using hdouble) ht
    have hmd : d ∣ m^2-1 := (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt (by positivity))).mp
      (show 1 ≡ m^2 [MOD d] by simpa using hloc.symm)
    have hdm : d ∈ (m^2-1).divisors := Nat.mem_divisors.mpr ⟨hmd, (Nat.sub_pos_of_lt ((show 1 < m by omega).trans_le (Nat.le_pow (by decide)))).ne'⟩
    have hdiv : a m ∣ (m^2-1)/d+4*m^2*(d-1) := by
      have hcancel := Nat.mul_div_cancel' hmd
      have hprod : d*((m^2-1)/d+4*m^2*(d-1)) = (m*p)^2-1 := by
        have hback : (m^2-1)+1 = m^2 := Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))
        have hpback : ((m*p)^2-1)+1 = (m*p)^2 :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (Nat.mul_pos hm hp.pos) 2))
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
        have hpred : d-1=k := by omega
        have hpk : p=2*k+1 := by omega
        rw [Nat.mul_add, hcancel, hpred, hk, hpk]
        rw [hpk] at hpback
        nlinarith only [hback,hpback]
      apply Nat.dvd_of_mul_dvd_mul_left (show 0 < d by omega)
      rw [hprod, mul_comm d]
      exact hdvd
    have reject := hone m d hmo hmc hdm (hpval ▸ hp) (hpval ▸ hcp)
      (fun q hq => hpval ▸ hmax q hq) hdiv
    exact reject (by simpa [d] using hlast)
  · have h := cleared p e hp hpodd
    obtain ⟨hloc,hother⟩ := two_residues hpos h ht
    have hb := power_bound hp.two_le hm2 (by omega) h hloc
    have hcop : p.Coprime (a m*a (p^e)-1) := by
      apply Nat.Coprime.of_dvd_left (show p ∣ m*p^e from
        (dvd_pow_self p he.ne').trans (dvd_mul_left _ _))
      apply Nat.coprime_of_mul_modEq_one (m*p^e)
      simpa only [← sq] using ht.of_dvd (dvd_mul_left _ _)
    apply hhigher m p e hmo hmc hp hpodd hcp hmax (by omega) hb hcop hloc hdvd
    by_cases parity : Even e <;> simp only [parity, if_true, if_false] at hother ⊢ <;>
      push_cast at hother ⊢ <;> exact hother

end OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R2
