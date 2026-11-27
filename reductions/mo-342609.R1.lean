import OMAStatements.S_mo_342609

open ArithmeticFunction Finset

namespace OMA.R_mo_342609_R1

/-- The diagonal case is the odd-square case of Iannucci's equation. -/
def H1 : Prop := ∀ u : ℕ, 1 < u → Odd u → IsSquare u →
  sigma 1 u ≠ u + u.totient

/-- A proper divisor leaves a specific quotient to test for being a power of two. -/
def H2 : Prop := ∀ u n : ℕ, Odd u → Odd n → n ∣ u → n < u → (n = 1 ∨ IsSquare u) →
  let U := u + u.totient
  let N := n + n.totient
  let D := sigma 1 u - U
  0 < D → D ∣ U-N →
  let q := (U-N)/D + 1
  q ≠ 2 ^ Nat.log 2 q

lemma odd_geom_mod (p : ℕ) (hp : Odd p) (k : ℕ) :
    (∑ j ∈ range k, p^j) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,Nat.add_mod,ih,Nat.odd_iff.mp (show Odd (p^k) from hp.pow)]
    omega

lemma square_of_odd_sigma (u : ℕ) (hu : Odd u) (hs : Odd (sigma 1 u)) : IsSquare u := by
  have hune : u ≠ 0 := by intro h; subst u; simp at hu
  have product := (sigma_one_apply u).trans (Nat.sum_divisors hune)
  have evenExp (p : ℕ) (hp : p ∈ u.primeFactors) : Even (u.factorization p) := by
    have hpdiv := Nat.dvd_of_mem_primeFactors hp
    have hpo : Odd p := by
      by_contra! hnot
      have : 2 ∣ u := dvd_trans (Even.two_dvd (Nat.not_odd_iff_even.mp hnot)) hpdiv
      exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr this)
    by_contra hne
    have hoe := Nat.not_even_iff_odd.mp hne
    have hd : (∑ j ∈ range (u.factorization p + 1), p^j) ∣ sigma 1 u := by
      rw [product]
      exact Finset.dvd_prod_of_mem _ hp
    have he : 2 ∣ (∑ j ∈ range (u.factorization p + 1), p^j) := by
      apply Nat.dvd_of_mod_eq_zero
      rw [odd_geom_mod p hpo]; have := Nat.odd_iff.mp hoe; omega
    exact (Nat.not_even_iff_odd.mpr hs) (even_iff_two_dvd.mpr (dvd_trans he hd))
  refine ⟨∏ p ∈ u.primeFactors, p^(u.factorization p/2), ?_⟩
  calc
    u = ∏ p ∈ u.primeFactors, p^u.factorization p := Nat.prod_primeFactors_pow_factorization hune
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_add]
      congr 1
      obtain ⟨d,hd⟩ := evenExp p hp
      omega

lemma sigma_two (a : ℕ) : sigma 1 (2^a) = 2^(a+1)-1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  have h (k : ℕ) : (∑ j ∈ range k, 2^j) + 1 = 2^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ,pow_succ]; omega
  have := h (a+1)
  omega

lemma quotient_test {T S U N : ℕ} (hT : 1 < T) (hN : N < U)
    (h : (T-1)*S+N=T*U) :
    0 < S-U ∧ S-U ∣ U-N ∧ (U-N)/(S-U)+1 = T := by
  have ht : T-1+1 = T := by omega
  have eq : (T-1)*S+N=(T-1)*U+U := by
    calc _ = T*U := h
         _ = (T-1+1)*U := by rw [ht]
         _ = _ := by ring
  have hs : U<S := by
    by_contra! hle
    have := Nat.mul_le_mul_left (T-1) hle
    omega
  have hd : (S-U)*(T-1) = U-N := by
    have e := Nat.sub_add_cancel hs.le
    have m := congrArg (fun k => (T-1)*k) e
    simp only [Nat.mul_add] at m
    rw [mul_comm (S-U)]
    omega
  refine ⟨by omega,⟨T-1,hd.symm⟩,?_⟩
  rw [← hd,Nat.mul_div_cancel_left _ (by omega : 0<S-U),ht]

lemma normalized_iff (R n a u : ℕ) (hR : 0<R) (hu : Odd u) (prod : R*n=2^a*u) :
    (n.totient + sigma 1 (R*n) = (2*R-1)*n + (4*R*n).totient) ↔
    (2^(a+1)-1)*sigma 1 u+(n+n.totient)=2^(a+1)*(u+u.totient) := by
  let T := 2^(a+1)
  have cop : Nat.Coprime 2 u := Nat.coprime_two_left.mpr hu
  have sig : sigma 1 (R*n) = (T-1)*sigma 1 u := by
    rw [prod,isMultiplicative_sigma.map_mul_of_coprime (cop.pow_left _),sigma_two]
  have tot : (4*R*n).totient = T*u.totient := by
    have e : 4*R*n = 2^(a+2)*u := by
      rw [mul_assoc,prod,pow_succ,pow_succ];ring
    rw [e,Nat.totient_mul (cop.pow_left _),Nat.totient_prime_pow_succ Nat.prime_two]
    simp [T]
  have first : (2*R-1)*n+n=T*u := by
    calc (2*R-1)*n+n = (2*R-1+1)*n := by ring
         _ = 2*(R*n) := by rw [show 2*R-1+1=2*R by omega];ring
         _ = T*u := by rw [prod];dsimp [T];ring
  change _ ↔ (T-1)*sigma 1 u+(n+n.totient)=T*(u+u.totient)
  rw [sig,tot,Nat.mul_add]
  omega

lemma recover_quotient {T S U N : ℕ} (hN : N < U) (hp : 0 < S-U)
    (hd : S-U ∣ U-N) (hq : (U-N)/(S-U)+1=T) : (T-1)*S+N=T*U := by
  have mul := Nat.div_mul_cancel hd
  let k := (U-N)/(S-U)
  have a : k*(S-U)=U-N := mul
  have b := congrArg (k*·) (Nat.sub_add_cancel (by omega : U≤S))
  simp only [Nat.mul_add] at b
  change k+1=T at hq
  rw [← hq,Nat.add_sub_cancel,Nat.add_mul,one_mul]
  omega

lemma odd_obstruction (h₁ : H1) (h₂ : H2) (R n : ℕ) (hR : 0<R) (hn : 0<n)
    (he : n.totient + sigma 1 (R*n) = (2*R-1)*n + (4*R*n).totient) : Even n := by
  by_contra hne
  have nodd := Nat.not_even_iff_odd.mp hne
  obtain ⟨a,r,ro,hr⟩ := Nat.exists_eq_two_pow_mul_odd hR.ne'
  let u := r*n
  let T := 2^(a+1)
  have uodd : Odd u := ro.mul nodd
  have up : 0<u := by dsimp [u]; exact Nat.mul_pos (by have := Nat.odd_iff.mp ro; omega) hn
  have nd : n ∣ u := dvd_mul_left _ _
  have nu : n ≤ u := Nat.le_of_dvd up nd
  have phile : n.totient ≤ u.totient := Nat.le_of_dvd (Nat.totient_pos.mpr up) (Nat.totient_dvd_of_dvd nd)
  have prod : R*n = 2^a*u := by rw [hr]; dsimp [u]; ring
  have tpos : 1<T := by dsimp [T]; exact Nat.one_lt_pow (by omega) (by decide)
  have teven : Even T := by dsimp [T]; rw [pow_succ]; exact even_two.mul_left _
  have normEq := (normalized_iff R n a u hR uodd prod).mp he
  change (T-1)*sigma 1 u+(n+n.totient)=T*(u+u.totient) at normEq
  have square : n=1 ∨ IsSquare u := by
    by_cases h : n=1
    · exact Or.inl h
    right
    apply square_of_odd_sigma _ uodd
    by_contra no
    have hn2 : 2<n := by have := Nat.odd_iff.mp nodd;omega
    have oddL : Odd ((T-1)*sigma 1 u+(n+n.totient)) :=
      ((Nat.not_odd_iff_even.mp no).mul_left _).add_odd (nodd.add_even (Nat.totient_even hn2))
    have evenR : Even (T*(u+u.totient)) := teven.mul_right _
    rw [normEq] at oddL
    exact (Nat.not_even_iff_odd.mpr oddL) evenR
  rcases eq_or_lt_of_le nu with eq|lt
  · have eq' : sigma 1 u = u+u.totient := by
      rw [eq] at normEq
      have et := congrArg (fun z => z*(u+u.totient)) (show T-1+1=T by omega)
      simp only [Nat.add_mul,one_mul] at et
      have e : (T-1)*sigma 1 u=(T-1)*(u+u.totient) := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) e
    rcases square with h|sq
    · have : u=1 := eq.symm.trans h
      simp [this] at eq'
    · by_cases one : u=1
      · simp [one] at eq'
      · exact h₁ u (by omega) uodd sq eq'
  · have detail := quotient_test tpos (by omega : n+n.totient < u+u.totient) normEq
    obtain ⟨hp,hd,hq⟩ := detail
    have impossible := h₂ u n uodd nodd nd lt square hp hd
    dsimp only at impossible
    rw [hq] at impossible
    exact impossible (by dsimp [T];rw [Nat.log_pow (by decide : 1<2)])

theorem main : H1 → H2 → type_of% @OMA.S_mo_342609.main := by
  intro h₁ h₂
  refine ⟨?_,fun R n hR hn h => odd_obstruction h₁ h₂ R n hR hn h⟩
  intro N n hN hpar hn h
  let R := (N+1)/2
  have hR : 0<R := by dsimp [R];omega
  apply odd_obstruction h₁ h₂ R n hR hn
  have e : 2*R-1 = N := by dsimp [R];omega
  have d : 4*R = 2*(N+1) := by dsimp [R];omega
  simpa only [e,d] using h

end OMA.R_mo_342609_R1
