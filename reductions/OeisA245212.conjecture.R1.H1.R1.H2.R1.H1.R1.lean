import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1
import Mathlib

/-!
Finite prime-power tests for the divisor-sum equation. For a complementary
factor m write W = Σ d τ(d) and S = σ(m). Removing p^e leaves a remainder
W−(p−1)S divisible by p^e. Two different exact prime-power blocks cannot
both have zero remainder. The two multiplicativity calculations are from
DomTheDeveloper's merged reduction #1048.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
namespace OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R1

private lemma moment_mul (u v : ℕ) (hc : u.Coprime v) :
    (∑ d ∈ (u*v).divisors, d * d.divisors.card) =
    (∑ d ∈ u.divisors, d * d.divisors.card) * (∑ d ∈ v.divisors, d * d.divisors.card) := by
  let F : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
  have hf : F.IsMultiplicative :=
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
  have he (n : ℕ) : F n = ∑ d ∈ n.divisors, d * d.divisors.card := by
    change ((ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta) n = _
    rw [ArithmeticFunction.mul_zeta_apply]
    simp only [pmul_apply, id_apply, sigma_zero_apply]
  simpa only [he] using hf.map_mul_of_coprime hc

private lemma moment_at_power (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^e).divisors, d * d.divisors.card) =
    ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.divisors_prime_pow hp, card_map, card_range]


private lemma power_formula (p e : ℕ) (hp : p.Prime) :
    (p-1)*(σ 1 (p^e))+1 = p^(e+1) ∧
    (p-1)*(∑ d ∈ (p^e).divisors,d*d.divisors.card)+σ 1 (p^e) = (e+1)*p^(e+1) := by
  rw [moment_at_power p e hp,sigma_apply_prime_pow hp]
  simp only [mul_one]
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  simp only [Nat.succ_eq_add_one,Nat.add_one_sub_one]
  induction e with
  | zero => simp
  | succ e ih =>
    obtain ⟨h₁,h₂⟩ := ih
    rw [sum_range_succ (fun j => (b+1)^j) (e+1),
      sum_range_succ (fun j => (b+1)^j*(j+1)) (e+1),pow_succ (b+1) (e+1)]
    constructor <;> nlinarith only [h₁,h₂]

private lemma coprime_sigma (p e : ℕ) (hp : p.Prime) : p.Coprime (σ 1 (p^e)) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  have hg := (power_formula p e hp).1
  have hd : p∣(p-1)*(σ 1 (p^e))+1 := by rw [hg]; exact dvd_pow_self p (by omega)
  have hn : p∣1 := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right h _)).mpr hd
  exact hp.ne_one (Nat.dvd_one.mp hn)

private lemma ratio (m p e : ℕ) (hp : p.Prime) (hc : m.Coprime p)
    (hz : (∑ d ∈ m.divisors,d*d.divisors.card) = (p-1)*(σ 1 m)) :
    ((∑ d ∈ (m*p^e).divisors,d*d.divisors.card)+σ 1 (m*p^e))*σ 1 (p^e) =
      ((e+1)*p^(e+1))*σ 1 (m*p^e) := by
  rw [moment_mul _ _ (hc.pow_right e),isMultiplicative_sigma.map_mul_of_coprime (hc.pow_right e),hz]
  calc
    _ = ((p-1)*(∑ d ∈ (p^e).divisors,d*d.divisors.card)+σ 1 (p^e))*
        ((σ 1 m)*(σ 1 (p^e))) := by ring
    _ = _ := by rw [(power_formula p e hp).2]

private lemma one_resonance (p q e f : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (heq : ((e+1)*p^(e+1))*(σ 1 (q^f)) = ((f+1)*q^(f+1))*(σ 1 (p^e))) : False := by
  have cop := (Nat.coprime_primes hp hq).mpr hne
  have get (a b i j : ℕ) (ha : a.Prime) (hc : a.Coprime b)
      (h : ((i+1)*a^(i+1))*(σ 1 (b^j)) = ((j+1)*b^(j+1))*(σ 1 (a^i))) :
      a^(i+1) ≤ j+1 := by
    have hdiv : a^(i+1) ∣ ((j+1)*b^(j+1))*(σ 1 (a^i)) := by
      rw [←h]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    rw [mul_assoc] at hdiv
    have hcop : (a^(i+1)).Coprime (b^(j+1) * σ 1 (a^i)) :=
      ((hc.pow_right _).mul_right (coprime_sigma _ _ ha)).pow_left _
    exact Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hdiv)
  have h₁ := get p q e f hp cop heq
  have h₂ := get q p f e hq cop.symm heq.symm
  have hp' := (e+1).lt_two_pow_self.trans_le (Nat.pow_le_pow_left hp.two_le (e+1))
  have hq' := (f+1).lt_two_pow_self.trans_le (Nat.pow_le_pow_left hq.two_le (f+1))
  omega

/-- Among the prime blocks of a non-prime-power at least one has a
nonzero remainder, even before imposing the divisor-sum equation. -/
private lemma pick (n : ℕ) (hn : 1 < n) (hnp : ¬IsPrimePow n) :
    ∃ p e m : ℕ, p.Prime ∧ 0 < e ∧ 0 < m ∧ m.Coprime p ∧ n=m*p^e ∧
      (∑ d ∈ m.divisors,d*d.divisors.card) ≠ (p-1)*(σ 1 m) := by
  have hn₀ : n≠0 := by omega
  have blocks (p : ℕ) (hp : p∈n.primeFactors) :
      ∃ e m : ℕ, 0 < e ∧ 0 < m ∧ m.Coprime p ∧ n=m*p^e := by
    have hpr := Nat.prime_of_mem_primeFactors hp
    refine ⟨n.factorization p,n/p^(n.factorization p),
      hpr.factorization_pos_of_dvd hn₀ (Nat.dvd_of_mem_primeFactors hp),
      Nat.ordCompl_pos p hn₀,(Nat.coprime_ordCompl hpr hn₀).symm,?_⟩
    exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm.trans (mul_comm _ _)
  obtain ⟨p,hp,q,hq,hpq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hnp
  obtain ⟨e,m,he,hm,hc,hem⟩ := blocks p hp
  obtain ⟨f,b,hf,hb,hc',hfb⟩ := blocks q hq
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hqq := Nat.prime_of_mem_primeFactors hq
  by_cases h₁ : (∑ d ∈ m.divisors,d*d.divisors.card) = (p-1)*(σ 1 m)
  · by_cases h₂ : (∑ d ∈ b.divisors,d*d.divisors.card) = (q-1)*(σ 1 b)
    · exfalso
      have hpR := ratio m p e hpp hc h₁
      have hqR := ratio b q f hqq hc' h₂
      rw [←hem] at hpR
      rw [←hfb] at hqR
      apply one_resonance p q e f hpp hqq hpq
      apply Nat.eq_of_mul_eq_mul_right (sigma_pos 1 n hn₀)
      calc
        _ = (((e+1)*p^(e+1))*σ 1 n)*σ 1 (q^f) := by ring
        _ = (((f+1)*q^(f+1))*σ 1 n)*σ 1 (p^e) := by rw [←hpR,←hqR];ring
        _ = _ := by ring
    · exact ⟨q,f,b,hqq,hf,hb,hc',hfb,h₂⟩
  · exact ⟨p,e,m,hpp,he,hm,hc,hem,h₁⟩

private lemma balance (m p e : ℕ) (hm : 0 < m) (hp : p.Prime) (hc : m.Coprime p)
    (eq : OeisA245212.a (m*p^e) = (σ 1 (m*p^e):ℤ)) :
    2*(m*m.divisors.card)*(e+1)*p^e =
      (∑ d ∈ m.divisors,d*d.divisors.card)*(∑ d ∈ (p^e).divisors,d*d.divisors.card) +
      (σ 1 m)*(σ 1 (p^e)) := by
  let n := m*p^e
  have hn : n≠0 := Nat.mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)
  have hsum : (∑ d ∈ n.divisors,d*d.divisors.card) =
      n*n.divisors.card+(∑ d ∈ n.properDivisors,d*d.divisors.card) := by
    calc
      _ = ∑ d ∈ insert n n.properDivisors,d*d.divisors.card := by rw [Nat.insert_self_properDivisors hn]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  change OeisA245212.a n = (σ 1 n:ℤ) at eq
  unfold OeisA245212.a at eq
  have hnat : 2*n*n.divisors.card=(∑ d ∈ n.divisors,d*d.divisors.card)+σ 1 n := by
    rw [hsum]
    have hz : (n:ℤ)*n.divisors.card = (∑ d ∈ n.properDivisors,(d:ℤ)*d.divisors.card)+(σ 1 n:ℤ) := by linarith
    have h' : n*n.divisors.card=(∑ d ∈ n.properDivisors,d*d.divisors.card)+σ 1 n := by exact_mod_cast hz
    nlinarith only [h']
  have hcard : (p^e).divisors.card = e+1 := by rw [Nat.divisors_prime_pow hp,card_map,card_range]
  dsimp only [n] at hnat
  rw [moment_mul _ _ (hc.pow_right e),isMultiplicative_sigma.map_mul_of_coprime (hc.pow_right e),
    (hc.pow_right e).card_divisors_mul,hcard] at hnat
  convert hnat using 1 <;> ring

private lemma eliminate (P X E T W S F G : ℤ)
    (bal : 2*T*(E+1)*X=W*F+S*G)
    (geo : (P-1)*G+1=P*X) (weighted : (P-1)*F+G=(E+1)*P*X) :
    W-(P-1)*S = X*(2*T*(E+1)*(P-1)^2 - W*((E+1)*P^2-(E+2)*P) - S*P*(P-1)) := by
  linear_combination -(P-1)^2*bal-W*(P-1)*weighted+(W-S*(P-1))*geo


/-- At exponent one there is at most one prime to test for each m. -/
def H1 : Prop := ∀ m p : ℕ, 0 < m → p.Prime → m.Coprime p →
  let W := ∑ d ∈ m.divisors,d*d.divisors.card
  let S := σ 1 m
  let D := 4*(m*m.divisors.card)-(2*W+S)
  0 < D → D∈(W+S).divisors → p=(W+S)/D →
  let n := m*p
  1 < n → Odd n → ¬ IsPrimePow n → 2*n.totient < n →
    (¬ ∃ p q e f : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 3≤p ∧ 5≤q ∧
      0 < e ∧ 0 < f ∧ n=p^e*q^f) →
    (¬ ∃ k p q r e f g : ℕ, 0 < k ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧
      5≤p ∧ p < q ∧ q < r ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ n=3^k*p^e*q^f*r^g) → False

/-- At higher exponents the prime divides W+S, and its entire power
must divide the absolute value of the nonzero remainder. -/
def H2 : Prop := ∀ m p e : ℕ, 0 < m → p.Prime → m.Coprime p → 2≤e →
  let W := ∑ d ∈ m.divisors,d*d.divisors.card
  let S := σ 1 m
  let R : ℤ := (W:ℤ)-((p:ℤ)-1)*S
  p ∈ (W+S).divisors → R≠0 → p^e ∈ R.natAbs.divisors →
  let n := m*p^e
  1 < n → Odd n → ¬ IsPrimePow n → 2*n.totient < n →
    (¬ ∃ p q e f : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ 3≤p ∧ 5≤q ∧
      0 < e ∧ 0 < f ∧ n=p^e*q^f) →
    (¬ ∃ k p q r e f g : ℕ, 0 < k ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧
      5≤p ∧ p < q ∧ q < r ∧ 0 < e ∧ 0 < f ∧ 0 < g ∧ n=3^k*p^e*q^f*r^g) →
  R ≠ (p:ℤ)^e * (2*((m*m.divisors.card:ℕ):ℤ)*(e+1)*((p:ℤ)-1)^2 -
    W*(((e:ℤ)+1)*(p:ℤ)^2-((e:ℤ)+2)*p) - S*(p:ℤ)*((p:ℤ)-1))

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1.H1 := by
  intro one more n hn ho hnp hφ htwo hfour eq
  obtain ⟨p,e,m,hp,he,hm,hc,rfl,hne⟩ := pick n hn hnp
  let W := ∑ d ∈ m.divisors,d*d.divisors.card
  let S := σ 1 m
  have hS : 0 < S := sigma_pos 1 m hm.ne'
  have bal := balance m p e hm hp hc eq
  change 2*(m*m.divisors.card)*(e+1)*p^e =
    W*(∑ d ∈ (p^e).divisors,d*d.divisors.card)+S*(σ 1 (p^e)) at bal
  by_cases he₁ : e=1
  · subst e
    have hF : (∑ d ∈ (p^1).divisors,d*d.divisors.card)=1+2*p := by
      rw [moment_at_power p 1 hp]
      simp [sum_range_succ,mul_comm]
    have hG : σ 1 (p^1)=1+p := by rw [sigma_apply_prime_pow hp];simp [sum_range_succ]
    rw [hF,hG] at bal
    simp only [pow_one] at hn ho hnp hφ htwo hfour bal
    let T := m*m.divisors.card
    have hstar : 4*T*p=(W+S)+(2*W+S)*p := by dsimp only [T]; nlinarith only [bal]
    have hbig : 2*W+S < 4*T := by
      by_contra! h
      have := Nat.mul_le_mul_right p h
      omega
    let D := 4*T-(2*W+S)
    have hD : 0 < D := Nat.sub_pos_of_lt hbig
    have hd : D+(2*W+S)=4*T := Nat.sub_add_cancel hbig.le
    have hprod : p*D=W+S := by nlinarith only [hstar,congrArg (·*p) hd]
    have hmem : D∈(W+S).divisors := Nat.mem_divisors.mpr
      ⟨⟨p,by rw [←hprod,mul_comm]⟩,by omega⟩
    have hquot : p=(W+S)/D := by rw [←hprod,Nat.mul_div_cancel _ hD]
    exact one m p hm hp hc hD hmem hquot hn ho hnp hφ htwo hfour
  · let R : ℤ := (W:ℤ)-((p:ℤ)-1)*S
    have hpcast : ((p-1:ℕ):ℤ)=(p:ℤ)-1 := by rw [Nat.cast_sub hp.one_lt.le];norm_num
    have hR : R≠0 := by
      intro h
      apply hne
      change (W:ℤ)-((p:ℤ)-1)*S=0 at h
      have hh : (W:ℤ)=((p-1:ℕ):ℤ)*(S:ℤ) := by rw [hpcast];linarith
      exact_mod_cast hh
    obtain ⟨hg,hw⟩ := power_formula p e hp
    let F := ∑ d ∈ (p^e).divisors,d*d.divisors.card
    let G := σ 1 (p^e)
    have hz : (2:ℤ)*((m*m.divisors.card:ℕ):ℤ)*((e:ℤ)+1)*(p:ℤ)^e =
        (W:ℤ)*F+(S:ℤ)*G := by exact_mod_cast bal
    have hg' : ((p:ℤ)-1)*G+1=(p:ℤ)*(p:ℤ)^e := by
      rw [←hpcast,mul_comm (p:ℤ),←pow_succ]; exact_mod_cast hg
    have hw' : ((p:ℤ)-1)*F+G=((e:ℤ)+1)*p*(p:ℤ)^e := by
      rw [←hpcast,mul_assoc,mul_comm (p:ℤ) _,←pow_succ];exact_mod_cast hw
    have h := eliminate _ _ _ _ _ _ _ _ hz hg' hw'
    change R = _ at h
    have hd : (p:ℤ)^e ∣ R := ⟨_,h⟩
    have hdp : p^e ∣ R.natAbs := by
      obtain ⟨v,hv⟩ := hd
      exact ⟨v.natAbs,by rw [hv,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]⟩
    have hpd : (p:ℤ)∣(W:ℤ)+S := by
      have hb := dvd_add ((dvd_pow_self (p:ℤ) he.ne').trans hd) (dvd_mul_right (p:ℤ) (S:ℤ))
      have hsum : (W:ℤ)+S = R+(p:ℤ)*S := by dsimp only [R]; ring
      rw [hsum]
      exact hb
    have hpd' : p∣W+S := by exact_mod_cast hpd
    have hmem := Nat.mem_divisors.mpr ⟨hpd',show W+S≠0 by omega⟩
    have hmem' := Nat.mem_divisors.mpr ⟨hdp,Int.natAbs_ne_zero.mpr hR⟩
    exact more m p e hm hp hc (by omega) hmem hR hmem' hn ho hnp hφ htwo hfour h

end OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R1
