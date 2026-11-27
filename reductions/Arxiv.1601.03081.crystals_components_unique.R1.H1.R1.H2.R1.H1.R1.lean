import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1

/-! The quotient-four branch of crystal component uniqueness. -/

namespace CrystalQuotientFour

theorem consecutive_squares {c b : ℕ} (hc : Odd c) (hb : Odd b)
    (hcb : c ≤ b) (h : (c+b)^2 = 4*((c+1)*(b+1))) :
    ∃ t : ℕ, c+1 = 2*t^2 ∧ b+1 = 2*(t+1)^2 := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨v, hv⟩ := hb
  have huv : u ≤ v := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le huv
  have hdif : b = c + 2*d := by omega
  have h' : ((c : ℤ)+(b : ℤ))^2 = 4*(((c : ℤ)+1)*(b+1)) := by exact_mod_cast h
  have hdif' : (b : ℤ) = (c : ℤ) + 2*d := by exact_mod_cast hdif
  have hd2' : (d : ℤ)^2 = (c : ℤ)+b+1 := by
    rw [hdif'] at h' ⊢
    nlinarith only [h']
  have hd2 : d^2 = c+b+1 := by exact_mod_cast hd2'
  have hodd : Odd (d^2) := by
    rw [hd2]
    exact ⟨u+v+1, by omega⟩
  have hoddd : Odd d := Nat.Odd.of_mul_left (by simpa only [pow_two] using hodd)
  obtain ⟨t, ht⟩ := hoddd
  have ht' : (d : ℤ) = 2*(t : ℤ)+1 := by exact_mod_cast ht
  refine ⟨t, ?_, ?_⟩
  · exact_mod_cast (show (c : ℤ)+1 = 2*(t : ℤ)^2 by
      rw [ht', hdif', ht'] at hd2'
      nlinarith only [hd2'])
  · exact_mod_cast (show (b : ℤ)+1 = 2*((t : ℤ)+1)^2 by
      rw [ht', hdif', ht'] at hd2'
      nlinarith only [hd2', hdif', ht'])


theorem gcd_dvd_quotient {c b q : ℕ} (h : (c+b)^2 = q*((c+1)*(b+1))) :
    c.gcd b ∣ q := by
  have hc := Nat.gcd_dvd_left c b
  have hb := Nat.gcd_dvd_right c b
  have hs : c.gcd b ∣ (c+b)^2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left (dvd_add hc hb) _
  have ht : c.gcd b ∣ q*c*b+q*c+q*b :=
    dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hc _) _)
      (dvd_mul_of_dvd_right hc _)) (dvd_mul_of_dvd_right hb _)
  refine (Nat.dvd_add_iff_right ht).mpr ?_
  convert hs using 1
  rw [h]
  ring

theorem coprime_of_quotient_four {c b : ℕ} (hc : Odd c)
    (h : (c+b)^2 = 4*((c+1)*(b+1))) : c.Coprime b := by
  change c.gcd b = 1
  have hdvd := gcd_dvd_quotient h
  have hle : c.gcd b ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hodd : Odd (c.gcd b) := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left c b
    exact Nat.Odd.of_mul_left (hk ▸ hc)
  interval_cases hval : c.gcd b <;> simp_all <;> obtain ⟨k, hk⟩ := hodd <;> omega


theorem prime_mod_eight_of_twice_square {p n t : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ n) (ht : n+1 = 2*t^2) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : (n : ZMod p) = 0 := by
    obtain ⟨k,rfl⟩ := hpd
    simp
  have htz : (n : ZMod p)+1 = 2*(t : ZMod p)^2 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using
      congrArg (fun k : ℕ => (k : ZMod p)) ht
  rw [hn,zero_add] at htz
  apply (ZMod.exists_sq_eq_two_iff hp2).mp
  refine ⟨2*(t : ZMod p), ?_⟩
  linear_combination 2*htz

theorem prime_mod_eight_of_quotient_four {a b p : ℕ}
    (ha : Odd a) (hb : Odd b) (hab : a ≤ b)
    (hq : (a+b)^2 = 4*((a+1)*(b+1)))
    (hp : p.Prime) (hpd : p ∣ a ∨ p ∣ b) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  obtain ⟨t,hta,htb⟩ := consecutive_squares ha hb hab hq
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    rcases hpd with hd | hd
    · obtain ⟨j,hj⟩ := hd
      obtain ⟨k,hk⟩ := ha
      omega
    · obtain ⟨j,hj⟩ := hd
      obtain ⟨k,hk⟩ := hb
      omega
  rcases hpd with hpd | hpd
  · exact prime_mod_eight_of_twice_square hp hp2 hpd hta
  · exact prime_mod_eight_of_twice_square hp hp2 hpd htb


theorem scaled_difference_congruence {g x y z : ℕ} {r s : ℤ}
    (hgy : Odd (g*y)) (hxz : Odd (x*z)) (ho : g*y ≤ x*z)
    (hq : (g*y+x*z)^2 = 4*((g*y+1)*(x*z+1)))
    (hs : ((x : ℤ)*z+1)*s = ((g : ℤ)*y-1)^2) :
    (y : ℤ) ∣ (((x : ℤ)^3*s-(y : ℤ)^3*r)-3*(x : ℤ)^3)^2-8*(x : ℤ)^6 := by
  obtain ⟨t, hfirst, hsecond⟩ := consecutive_squares hgy hxz ho hq
  have hfirst' : (g : ℤ)*y+1 = 2*(t : ℤ)^2 := by exact_mod_cast hfirst
  have hsecond' : (x : ℤ)*z+1 = 2*((t : ℤ)+1)^2 := by exact_mod_cast hsecond
  have hs' : s = 2*((t : ℤ)-1)^2 := by
    have hsub : (g : ℤ)*y-1 = 2*(t : ℤ)^2-2 := by linarith only [hfirst']
    apply mul_left_cancel₀ (show (x : ℤ)*z+1 ≠ 0 by positivity)
    rw [hs, hsub, hsecond']
    ring
  have ht : (y : ℤ) ∣ 2*(t : ℤ)^2-1 := ⟨g, by linear_combination -hfirst'⟩
  let U := (x : ℤ)^3*s-(y : ℤ)^3*r-3*(x : ℤ)^3
  let V := 4*(x : ℤ)^3*t
  have hUV : (y : ℤ) ∣ U+V := ⟨(g : ℤ)*x^3-(y : ℤ)^2*r, by
    dsimp [U,V]
    linear_combination (x : ℤ)^3*hs'-(x : ℤ)^3*hfirst'⟩
  change (y : ℤ) ∣ U^2-8*(x : ℤ)^6
  rw [show U^2-8*(x : ℤ)^6 =
      (U-V)*(U+V)+(8*(x : ℤ)^6)*(2*(t : ℤ)^2-1) by dsimp [V]; ring]
  exact dvd_add (dvd_mul_of_dvd_right hUV (U-V))
    (dvd_mul_of_dvd_right ht (8*(x : ℤ)^6))


theorem fixed_difference_bound {y : ℕ} {d : ℤ}
    (h : (y : ℤ) ∣ (d-3)^2-8) : y ≤ ((d-3)^2-8).natAbs := by
  have hn : (d-3)^2-8 ≠ 0 := by
    intro he
    have he' : (d-3)^2 = 8 := sub_eq_zero.mp he
    have hs : (d-3).natAbs^2 = 8 := by
      calc
        (d-3).natAbs^2 = ((d-3)^2).natAbs := (Int.natAbs_pow _ _).symm
        _ = (8 : ℤ).natAbs := congrArg Int.natAbs he'
        _ = 8 := by decide +kernel
    have hroot : (d-3).natAbs = 2 := by
      rw [← Nat.sqrt_eq' (d-3).natAbs, hs]
      exact (Nat.eq_sqrt'.2 ⟨by decide, by decide⟩).symm
    rw [hroot] at hs
    norm_num at hs
  have hpos : 0 < ((d-3)^2-8).natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨k,hk⟩ := h
  have hk' : ((d-3)^2-8).natAbs = y*k.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hk
  exact Nat.le_of_dvd hpos ⟨k.natAbs,hk'⟩

theorem difference_at_least_ten {y d : ℕ} (hy : 33 ≤ y) (hd : 0 < d)
    (he : d % 2 = 0) (hc : (y : ℤ) ∣ ((d : ℤ)-3)^2-8) : 10 ≤ d := by
  by_contra! hl
  have hb := fixed_difference_bound hc
  interval_cases d <;> (try norm_num at he) <;> norm_num at hb <;> omega



theorem largeComponent_dvd (a b : ℕ)
    (h : (a+1)*(b+1) ∣ (a+b)^2) : (b : ℤ)+1 ∣ ((a : ℤ)-1)^2 := by
  have hs : b+1 ∣ (a+b)^2 := (dvd_mul_left (b+1) (a+1)).trans h
  have hs' : (b : ℤ)+1 ∣ ((a : ℤ)+b)^2 := by exact_mod_cast hs
  have hrewrite : ((a : ℤ)-1)^2 =
      ((a : ℤ)+b)^2 - ((b : ℤ)+1)*(2*(a : ℤ)+b-1) := by ring
  rw [hrewrite]
  exact dvd_sub hs' (dvd_mul_right _ _)

private theorem odd_sum_square_conflict {u v : ℕ}
    (huv : Odd (u+v)) (h4 : (u+v)^2 = 4*((u+1)*(v+1))) : False := by
  have ho : Odd ((u+v)^2) := huv.pow
  have he : Even ((u+v)^2) := by
    refine ⟨2*((u+1)*(v+1)), ?_⟩
    rw [h4]
    ring
  obtain ⟨x,hx⟩ := ho
  obtain ⟨y,hy⟩ := he
  omega

private theorem odd_second_pair {a c m : ℕ} (hm : Odd m)
    (hac : Nat.Coprime a c)
    (h4 : (c+m*a)^2 = 4*((c+1)*(m*a+1))) : Odd c ∧ Odd (m*a) := by
  rcases Nat.even_or_odd c with hcE | hcO
  · have haO : Odd a := by
      rcases Nat.even_or_odd a with haE | haO
      · change Nat.gcd a c = 1 at hac
        obtain ⟨u,hu⟩ := haE
        obtain ⟨v,hv⟩ := hcE
        have h2a : 2 ∣ a := ⟨u, by omega⟩
        have h2c : 2 ∣ c := ⟨v, by omega⟩
        have hdiv : 2 ∣ Nat.gcd a c := Nat.dvd_gcd h2a h2c
        rw [hac] at hdiv
        norm_num at hdiv
      · exact haO
    have hmaO : Odd (m*a) := hm.mul haO
    have hsum : Odd (c+m*a) := by
      obtain ⟨u,hu⟩ := hcE
      obtain ⟨v,hv⟩ := hmaO
      exact ⟨u+v, by omega⟩
    exact (odd_sum_square_conflict hsum h4).elim
  · have hmaO : Odd (m*a) := by
      rcases Nat.even_or_odd (m*a) with hmaE | hmaO
      · have hsum : Odd (c+m*a) := by
          obtain ⟨u,hu⟩ := hcO
          obtain ⟨v,hv⟩ := hmaE
          exact ⟨u+v, by omega⟩
        exact (odd_sum_square_conflict hsum h4).elim
      · exact hmaO
    exact ⟨hcO,hmaO⟩

private theorem odd_square_mod_eight {t : ℕ} (ht : Odd t) : t^2 % 8 = 1 := by
  obtain ⟨k,hk⟩ := ht
  have hk' : t = 2*k+1 := by omega
  rcases Nat.even_or_odd k with hke | hko
  · obtain ⟨j,hj⟩ := hke
    have hj' : k = 2*j := by omega
    rw [hk',hj']
    have heq : (2*(2*j)+1)^2 = 8*(2*j^2+j)+1 := by ring
    rw [heq]
    omega
  · obtain ⟨j,hj⟩ := hko
    have hj' : k = 2*j+1 := by omega
    rw [hk',hj']
    have heq : (2*(2*j+1)+1)^2 = 8*(2*j^2+3*j+1)+1 := by ring
    rw [heq]
    omega

private theorem twice_square_mod_eight_of_even {t : ℕ} (ht : Even t) :
    2*t^2 % 8 = 0 := by
  obtain ⟨k,hk⟩ := ht
  have hk' : t = 2*k := by omega
  rw [hk']
  have heq : 2*(2*k)^2 = 8*k^2 := by ring
  rw [heq]
  omega

private theorem odd_parameter_residues {a c m t : ℕ}
    (htc : c+1 = 2*t^2) (htma : m*a+1 = 2*(t+1)^2) (ht : Odd t) :
    c % 8 = 1 ∧ (m*a) % 8 = 7 := by
  have hcmodEq := congrArg (fun n : ℕ => n % 8) htc
  have hcplus : (c+1) % 8 = 2 := by
    simpa [Nat.add_mod, Nat.mul_mod, odd_square_mod_eight ht] using hcmodEq
  have hsucc : Even (t+1) := by
    obtain ⟨k,hk⟩ := ht
    exact ⟨k+1, by omega⟩
  have hmaModEq := congrArg (fun n : ℕ => n % 8) htma
  have hmaplus : (m*a+1) % 8 = 0 := by
    simpa [Nat.add_mod, twice_square_mod_eight_of_even hsucc] using hmaModEq
  constructor <;> omega

private theorem even_parameter_residues {a c m t : ℕ}
    (htc : c+1 = 2*t^2) (htma : m*a+1 = 2*(t+1)^2) (ht : Even t) :
    c % 8 = 7 ∧ (m*a) % 8 = 1 := by
  have hcmodEq := congrArg (fun n : ℕ => n % 8) htc
  have hcplus : (c+1) % 8 = 0 := by
    simpa [Nat.add_mod, twice_square_mod_eight_of_even ht] using hcmodEq
  have hsucc : Odd (t+1) := by
    obtain ⟨k,hk⟩ := ht
    exact ⟨k, by omega⟩
  have hmaModEq := congrArg (fun n : ℕ => n % 8) htma
  have hmaplus : (m*a+1) % 8 = 2 := by
    simpa [Nat.add_mod, Nat.mul_mod, odd_square_mod_eight hsucc] using hmaModEq
  constructor <;> omega

private theorem first_quotient_ge_sixteen {a c m p t : ℕ}
    (ha : 3 ≤ a) (hm : 21 ≤ m) (htc : c+1 = 2*t^2)
    (htma : m*a+1 = 2*(t+1)^2)
    (hfirst : (a+m*c)^2 = p*((a+1)*(m*c+1))) : 16 ≤ p := by
  have hmaNat : 63 ≤ m*a := by
    calc
      63 = 21*3 := by norm_num
      _ ≤ m*3 := Nat.mul_le_mul_right 3 hm
      _ ≤ m*a := Nat.mul_le_mul_left m ha
  have ht5 : 5 ≤ t := by
    by_contra h
    have ht4 : t ≤ 4 := by omega
    nlinarith [hmaNat, htma]
  have hmZ : (21 : ℤ) ≤ m := by exact_mod_cast hm
  have haZ : (3 : ℤ) ≤ a := by exact_mod_cast ha
  have htZ : (5 : ℤ) ≤ t := by exact_mod_cast ht5
  have htcZ : (c : ℤ)+1 = 2*(t : ℤ)^2 := by exact_mod_cast htc
  have htmaZ : (m : ℤ)*(a : ℤ)+1 = 2*((t : ℤ)+1)^2 := by
    exact_mod_cast htma
  have hca2 : (m : ℤ)*(a : ℤ) ≤ 2*c := by
    nlinarith [sq_nonneg ((t : ℤ)-5)]
  have hmSq : 441 ≤ (m : ℤ)^2 := by nlinarith
  have hprod : 441*a ≤ 2*(m : ℤ)*c := by
    calc
      441*a ≤ (m : ℤ)^2*a := mul_le_mul_of_nonneg_right hmSq (by positivity)
      _ = (m : ℤ)*((m : ℤ)*a) := by ring
      _ ≤ (m : ℤ)*(2*c) := mul_le_mul_of_nonneg_left hca2 (by positivity)
      _ = 2*(m : ℤ)*c := by ring
  have hbound : 32*((a : ℤ)+1) ≤ (m : ℤ)*c := by nlinarith [hprod, haZ]
  have hden : 16*((a : ℤ)+1)*((m : ℤ)*c+1) ≤ ((m : ℤ)*c)^2 := by
    have hplus : (m : ℤ)*c+1 ≤ 2*((m : ℤ)*c) := by omega
    have hmul := mul_le_mul_of_nonneg_right hbound (by positivity : (0 : ℤ) ≤ (m : ℤ)*c)
    calc
      _ ≤ 16*((a : ℤ)+1)*(2*((m : ℤ)*c)) :=
        mul_le_mul_of_nonneg_left hplus (by positivity)
      _ = 32*((a : ℤ)+1)*((m : ℤ)*c) := by ring
      _ ≤ ((m : ℤ)*c)^2 := by nlinarith [hmul]
  have hnum : 16*((a : ℤ)+1)*((m : ℤ)*c+1) ≤
      ((a : ℤ)+(m : ℤ)*c)^2 := by nlinarith [hden]
  have hfirstZ : ((a : ℤ)+(m : ℤ)*c)^2 =
      (p : ℤ)*(((a : ℤ)+1)*((m : ℤ)*c+1)) := by exact_mod_cast hfirst
  have hmul : 16*(((a : ℤ)+1)*((m : ℤ)*c+1)) ≤
      (p : ℤ)*(((a : ℤ)+1)*((m : ℤ)*c+1)) := by
    rw [← hfirstZ]
    nlinarith [hnum]
  have hpZ : (16 : ℤ) ≤ p :=
    le_of_mul_le_mul_right hmul (by positivity : (0 : ℤ) <
      (((a : ℤ)+1)*((m : ℤ)*c+1)))
  exact_mod_cast hpZ

end CrystalQuotientFour

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1

open Arxiv.«1601.03081»
open CrystalQuotientFour

/-- The non-diagonal quotient-four case with odd square parameter. -/
def H1 : Prop :=
  ∀ a c m p t : ℕ, a < c → 21 ≤ m → Odd m → a.Coprime c →
    c ≤ m*a → 3 ≤ a → 5 ≤ c →
    (a+m*c)^2 = p*((a+1)*(m*c+1)) →
    (c+m*a)^2 = 4*((c+1)*(m*a+1)) →
    c+1 = 2*t^2 → m*a+1 = 2*(t+1)^2 → Nat.Coprime c (m*a) →
    (∀ ell : ℕ, ell.Prime → ell ∣ m ∨ ell ∣ c ∨ ell ∣ (m*a) →
      ell % 8 = 1 ∨ ell % 8 = 7) →
    ((m*c : ℤ)+1) ∣ ((a : ℤ)-1)^2 → 16 ≤ p →
    c % 8 = 1 ∧ (m*a) % 8 = 7 → Odd t → False

/-- The non-diagonal quotient-four case with even square parameter. -/
def H2 : Prop :=
  ∀ a c m p t : ℕ, a < c → 21 ≤ m → Odd m → a.Coprime c →
    c ≤ m*a → 3 ≤ a → 5 ≤ c →
    (a+m*c)^2 = p*((a+1)*(m*c+1)) →
    (c+m*a)^2 = 4*((c+1)*(m*a+1)) →
    c+1 = 2*t^2 → m*a+1 = 2*(t+1)^2 → Nat.Coprime c (m*a) →
    (∀ ell : ℕ, ell.Prime → ell ∣ m ∨ ell ∣ c ∨ ell ∣ (m*a) →
      ell % 8 = 1 ∨ ell % 8 = 7) →
    ((m*c : ℤ)+1) ∣ ((a : ℤ)-1)^2 → 16 ≤ p →
    c % 8 = 7 ∧ (m*a) % 8 = 1 → Even t → False

theorem main : H1 → H2 →
    OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1.H1 := by
  intro hodd heven a c m p q hm hmo hcop hac hca ha hc hfirst hsecond hq4
  by_cases heq : a = c
  · subst c
    have hden : 0 < (a+1)*(m*a+1) := by positivity
    have hmul : p*((a+1)*(m*a+1)) = q*((a+1)*(m*a+1)) := by
      calc
        _ = (a+m*a)^2 := hfirst.symm
        _ = q*((a+1)*(m*a+1)) := hsecond
    exact Nat.eq_of_mul_eq_mul_right hden hmul
  · have hac' : a < c := lt_of_le_of_ne hac heq
    have hq : (c+m*a)^2 = 4*((c+1)*(m*a+1)) := by
      simpa [hq4] using hsecond
    have hoddPair := odd_second_pair hmo hcop hq
    obtain ⟨t,htc,htma⟩ := consecutive_squares hoddPair.1 hoddPair.2
      hca hq
    have hcopma := coprime_of_quotient_four hoddPair.1 hq
    have hdivFirst : (a+1)*(m*c+1) ∣ (a+m*c)^2 :=
      ⟨p, by rw [hfirst]; ring⟩
    have hnormalized := largeComponent_dvd a (m*c) hdivFirst
    have hp16 := first_quotient_ge_sixteen ha hm htc htma hfirst
    have hprime : ∀ ell : ℕ, ell.Prime → ell ∣ m ∨ ell ∣ c ∨ ell ∣ (m*a) →
        ell % 8 = 1 ∨ ell % 8 = 7 := by
      intro ell hp hdiv
      apply prime_mod_eight_of_quotient_four hoddPair.1 hoddPair.2
        hca hq hp
      rcases hdiv with hmdiv | hcdiv | hmadiv
      · exact Or.inr (dvd_mul_of_dvd_left hmdiv a)
      · exact Or.inl hcdiv
      · exact Or.inr hmadiv
    rcases Nat.even_or_odd t with htE | htO
    · have hres := even_parameter_residues htc htma htE
      exact (heven a c m p t hac' hm hmo hcop hca ha hc hfirst hq htc htma
        hcopma hprime hnormalized hp16 hres htE).elim
    · have hres := odd_parameter_residues htc htma htO
      exact (hodd a c m p t hac' hm hmo hcop hca ha hc hfirst hq htc htma
        hcopma hprime hnormalized hp16 hres htO).elim

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1
