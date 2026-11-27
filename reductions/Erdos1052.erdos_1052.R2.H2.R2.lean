import OMAReductions.R_Erdos1052_erdos_1052_R2

/-!
# Prime factors occurring together in a fixed-core completion

Fix an odd powerful core c. Bound the smaller of any two prime factors
occurring together in the initial factor, and bound it independently in
each shifted simple prime. These two bounds imply finiteness of the
exponents in R2.H2, while allowing the largest prime in every factor
to grow. A simultaneous interval of exponents missing all small multiples
of primes forces the bound, even for supports of unbounded cardinality.

Credit: @ubuwaits
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R2

-- A bound for pairs of prime factors in the seed.
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 2^a+1 → min p r ≤ B

-- A bound for pairs of prime factors in one shift.
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ q ∈ S, ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 1+q → min p r ≤ B

/-- A whole interval of exponents excludes every bounded odd offset and denominator. -/
theorem prime_power_free_interval (D : ℕ) :
    ∃ W : ℕ, 2*D+1 < W ∧ ∀ E u d q k : ℕ, W ≤ E → E ≤ W+2*D →
      Odd u → u ≤ D → 0 < d → d ≤ D → q.Prime → d*q^k ≠ 2^E+u := by
  let L := 2*D+2
  let M := 2^(L+2*D)+D
  let P := (2*D+2)*(M^2).factorial
  have hP : 2*D+2 ≤ P := Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
  refine ⟨P+L,by dsimp [L]; omega,?_⟩
  intro E u d q k hlow hhigh hu hud hd hdD hq heq
  let e := E-P
  have he : E=e+P := by dsimp [e]; omega
  have hel : L ≤ e := by dsimp [e]; omega
  have heh : e ≤ L+2*D := by dsimp [e]; omega
  have he0 : 0 < e := by dsimp [L] at hel; omega
  let m := 2^e+u
  have hlo : D < 2^e := by
    have h := Nat.lt_two_pow_self (n:=e)
    dsimp [L] at hel; omega
  have hmododd : Odd m := (even_two.pow_of_ne_zero he0.ne').add_odd hu
  have hmD : D < m := by dsimp [m]; omega
  have hmm : m ≤ M := Nat.add_le_add (Nat.pow_le_pow_right (by decide) heh) hud
  have hm2 : Odd (m^2) := hmododd.pow
  have hmm2 : m^2 ≤ M^2 := Nat.pow_le_pow_left hmm _
  have hper : (m^2).totient ∣ P := dvd_mul_of_dvd_right
    (Nat.dvd_factorial ((Nat.totient_pos).mpr hm2.pos) ((Nat.totient_le _).trans hmm2)) _
  obtain ⟨z,hz⟩ := hper
  have hpmod : Nat.ModEq (m^2) (2^P) 1 := by
    rw [hz,pow_mul]
    simpa only [one_pow] using (Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hm2)).pow z
  have hpow := Nat.two_pow_pos P
  obtain ⟨b,hb⟩ := (Nat.modEq_iff_dvd' (show 1≤2^P by omega)).mp hpmod.symm
  have hpid : 2^P=m^2*b+1 := by omega
  let t := 1+2^e*m*b
  have hmt : m*t=d*q^k := by
    rw [heq,he,pow_add,hpid]
    dsimp [t,m]
    ring
  have hPbig : 2*D < 2^P := lt_trans (by omega) Nat.lt_two_pow_self
  have hbound : D*m < 2^E := calc
    D*m ≤ D*(2*2^e) := Nat.mul_le_mul_left _ (by dsimp [m]; omega)
    _ = 2*D*2^e := by ring
    _ < 2^P*2^e := Nat.mul_lt_mul_of_pos_right hPbig (Nat.two_pow_pos _)
    _ = _ := by rw [he,pow_add,Nat.mul_comm (2^P)]
  have htD : D<t := by
    by_contra! hx
    have hv := Nat.mul_le_mul_right m hx
    rw [Nat.mul_comm t m,hmt,heq] at hv
    omega
  have divides {x : ℕ} (hx : D<x) (hxq : x ∣ d*q^k) : q ∣ x := by
    by_contra hn
    have hcop := ((hq.coprime_iff_not_dvd.mpr hn).symm).pow_right k
    have := Nat.le_of_dvd hd (hcop.dvd_of_dvd_mul_right hxq)
    omega
  have hqm := divides hmD (hmt ▸ dvd_mul_right m t)
  have hqt := divides htD (hmt ▸ dvd_mul_left t m)
  have hqm' : q ∣ 2^e*m*b := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqm _) _
  have hbad : q ∣ 1 := (Nat.dvd_add_iff_left hqm').mpr hqt
  exact hq.not_dvd_one hbad

theorem prime_free_interval (D : ℕ) :
    ∃ W : ℕ, 2*D+1 < W ∧ ∀ E u d q : ℕ, W ≤ E → E ≤ W+2*D →
      Odd u → u ≤ D → 0 < d → d ≤ D → q.Prime → d*q ≠ 2^E+u := by
  obtain ⟨W,hW,h⟩ := prime_power_free_interval D
  exact ⟨W,hW,fun E u d q h1 h2 h3 h4 h5 h6 h7 => by
    simpa only [pow_one] using h E u d q 1 h1 h2 h3 h4 h5 h6 h7⟩

/-- One step of the chain. The offset is positive, odd, and never exceeds
the current denominator, so the loss of binary digits has a fixed bound. -/
theorem next_exponent {D E u d r : ℕ} (hu : 0<u) (huD : u≤d)
    (hdb : d≤D) (hodd : Odd d) (hr : Odd r)
    (he : 2*D+1 < E) (heq : d*r=2^E+u) :
    ∃ j w, j ≤ 2*D ∧ Odd w ∧ w ≤ d ∧ d*(ordCompl[2] (1+r))=2^(E-j)+w := by
  let j := (1+r).factorization 2
  have hshift : 2^j*(ordCompl[2] (1+r))=1+r := Nat.ordProj_mul_ordCompl_eq_self (1+r) 2
  have hjpos : 0<j := by
    have hnon : ¬ 2 ∣ (ordCompl[2] (1+r)) := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
    have h2 : 2 ∣ 1+r := by obtain ⟨z,hz⟩ := hr; omega
    by_contra! hx
    have hj0 : j=0 := by omega
    rw [hj0,pow_zero,one_mul] at hshift
    exact hnon (h2.trans (dvd_of_eq hshift.symm))
  have hx : d*(1+r)=2^E+(u+d) := by rw [Nat.mul_add,Nat.mul_one,heq]; omega
  have hjbound : j ≤ 2*D := by
    by_contra! H
    let k := 2*D+1
    have hkd : 2^k ∣ d*(1+r) := dvd_mul_of_dvd_right
      ((Nat.pow_dvd_pow 2 H).trans (hshift ▸ dvd_mul_right _ _)) d
    rw [hx] at hkd
    have := Nat.le_of_dvd (show 0<u+d by omega)
      ((Nat.dvd_add_iff_right (Nat.pow_dvd_pow 2 (show k≤E by dsimp [k]; omega))).mpr hkd)
    have hy := Nat.lt_two_pow_self (n:=k)
    dsimp [k] at hy this
    omega
  have hje : j<E := by omega
  have hv : 2^j ∣ u+d := (Nat.dvd_add_iff_right (Nat.pow_dvd_pow 2 hje.le)).mpr <| by
    rw [← hx,← hshift]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  obtain ⟨w,hw⟩ := hv
  have he2 : (2:ℕ)^E=2^j*2^(E-j) := by rw [← pow_add]; congr 1; omega
  have heq' : d*(ordCompl[2] (1+r))=2^(E-j)+w := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos j) <| calc
    2^j*(d*(ordCompl[2] (1+r)))=d*(2^j*(ordCompl[2] (1+r))) := by ac_rfl
    _ = d*(1+r) := congrArg (d*·) hshift
    _ = _ := by rw [hx,hw,he2,Nat.mul_add]
  have hdmod : ¬2 ∣ (ordCompl[2] (1+r)) := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have hod : Odd (d*(ordCompl[2] (1+r))) := hodd.mul (Nat.not_even_iff_odd.mp
    (fun H => hdmod (even_iff_two_dvd.mp H)))
  have how : Odd w := by
    have h2 : 2 ∣ (2:ℕ)^(E-j) := dvd_pow_self 2 (by omega)
    rw [heq'] at hod
    obtain ⟨z,hz⟩ := hod
    exact Nat.odd_iff.mpr (by omega)
  have hwle : w≤d := by
    have hh : 2 ≤ (2:ℕ)^j := Nat.le_pow hjpos
    have := Nat.mul_le_mul_right w hh
    omega
  exact ⟨j,w,hjbound,how,hwle,heq'⟩

theorem seed_divisibility {a c : ℕ} (ha : 0<a) (hc : Odd c) (S : Finset ℕ)
    (hbal : (∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p))*
      (∏ q ∈ S, (1+q)) = 2*(2^a*c)*(∏ q ∈ S, q)) :
    (2^a+1)*(∏ q ∈ S, ordCompl[2] (1+q)) ∣ c*∏ q ∈ S, q := by
  have hb : (2:ℕ)^a*c ≠ 0 := mul_ne_zero (Nat.two_pow_pos a).ne' hc.pos.ne'
  have h2c : ¬ 2 ∣ c := by obtain ⟨z,hz⟩ := hc; omega
  have h2b : 2 ∈ (2^a*c).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_mul_of_dvd_left (dvd_pow_self 2 ha.ne') _,hb⟩
  have hval : (2^a*c).factorization 2 = a := by
    rw [Nat.factorization_mul (Nat.two_pow_pos a).ne' hc.pos.ne', Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd h2c, Nat.add_zero]
  have hs : 2^a+1 ∣ ∏ p ∈ (2^a*c).primeFactors, (1+p^(2^a*c).factorization p) := by
    simpa only [hval,Nat.add_comm 1 (2^a)] using Finset.dvd_prod_of_mem
      (fun p : ℕ => 1+p^(2^a*c).factorization p) h2b
  have hdiv := Nat.mul_dvd_mul hs (Finset.prod_dvd_prod_of_dvd (s:=S) (fun q : ℕ => ordCompl[2] (1+q)) (fun q => 1+q)
    (fun q _ => Nat.ordCompl_dvd (1+q) 2))
  rw [hbal, show 2*(2^a*c)*(∏ q ∈ S, q) = 2^(a+1)*(c*∏ q ∈ S, q) by rw [pow_succ]; ac_rfl] at hdiv
  have hcop : (2^a+1).Coprime 2 :=
    Nat.coprime_two_right.mpr ((even_two.pow_of_ne_zero ha.ne').add_odd odd_one)
  have hprod : (∏ q ∈ S, ordCompl[2] (1+q)).Coprime 2 :=
    Nat.coprime_prod_left_iff.mpr (fun q _ =>
      (Nat.prime_two.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl Nat.prime_two (by omega : 1+q ≠ 0))).symm)
  exact ((hcop.mul_left hprod).pow_right (a+1)).dvd_of_dvd_mul_left hdiv

set_option maxHeartbeats 1800000 in
theorem bound_from_prime_pairs {B c : ℕ} (hB : 2≤B) (hc : 0<c)
    (hcB : ∀ p : ℕ, p.Prime → p ∣ c → p≤B) :
    ∃ W : ℕ, ∀ (S : Finset ℕ) (E : ℕ), 0<E →
      (∀ q ∈ S, q.Prime ∧ q ≠ 2) →
      (2^E+1)*(∏ q ∈ S, ordCompl[2] (1+q)) ∣ c*(∏ q ∈ S, q) →
      (∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 2^E+1 → min p r ≤ B) →
      (∀ q ∈ S, ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 1+q → min p r ≤ B) → E<W := by
  let demand (q : ℕ) := ordCompl[2] (1+q)
  let demands (S : Finset ℕ) := ∏ q ∈ S, demand q
  let primesProduct (S : Finset ℕ) := ∏ q ∈ S, q
  let primeSupport (S : Finset ℕ) := ∀ q ∈ S, q.Prime ∧ q ≠ 2
  have prime_mem_of_dvd {R : Finset ℕ} (hr : primeSupport R) {p : ℕ} (hp : p.Prime)
      (hd : p ∣ primesProduct R) : p ∈ R := by
    obtain ⟨q,hq,hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hd
    simpa only [((hr q hq).1.dvd_iff_eq hp.ne_one).mp hdiv] using hq
  let Smooth (B z : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ z → p ≤ B


  let OneLarge (B z : ℕ) : Prop :=
    ∃ t r : ℕ, z=t*r ∧ Smooth B t ∧ (r=1 ∨ r.Prime ∧ B<r)

  have smooth_mul {B u v : ℕ} (hu : Smooth B u) (hv : Smooth B v) : Smooth B (u*v) := by
    intro p hp h
    exact (hp.dvd_mul.mp h).elim (hu p hp) (hv p hp)

  have smooth_coprime {B d : ℕ} (hd : Smooth B d) {T : Finset ℕ}
      (hT : ∀ q ∈ T, q.Prime ∧ B<q) : d.Coprime (primesProduct T) :=
    Nat.coprime_prod_right_iff.mpr fun q hq =>
      ((hT q hq).1.coprime_iff_not_dvd.mpr (fun h => (hT q hq).2.not_ge (hd q (hT q hq).1 h))).symm
  have chain_bound {B D W : ℕ} (hB : 2 ≤ B) (hD : 0<D) (hsD : Smooth B D)
      (hW : 2*D+1<W)
      (hgap : ∀ E u d q : ℕ, W≤E → E≤W+2*D → Odd u → u≤D →
        0<d → d≤D → q.Prime → d*q ≠ 2^E+u)
      (T : Finset ℕ) (hT : ∀ r ∈ T, r.Prime ∧ B<r)
      (hthin : ∀ r ∈ T, OneLarge B (demand r)) {E u d H : ℕ}
      (hd : Odd d) (hH : Odd H) (hu : Odd u) (hud : u≤d) (hsd : Smooth B d)
      (hone : OneLarge B H) (heq : d*H=2^E+u)
      (hbudget : d*H*demands T ∣ D*primesProduct T) : E<W := by
    induction T using Finset.strongInductionOn generalizing E u d H with
    | _ T ih =>
      by_contra! hWE
      obtain ⟨t,r,hfac,hts,hr⟩ := hone
      have ht : Odd t := hH.of_dvd_nat (hfac ▸ dvd_mul_right _ _)
      have hsdt := smooth_mul hsd hts
      have hdtleft : d*t ∣ d*H*demands T := by
        refine ⟨r*demands T,?_⟩
        rw [hfac]; ac_rfl
      have hdtD := (smooth_coprime hsdt hT).dvd_of_dvd_mul_right (hdtleft.trans hbudget)
      have hdtle := Nat.le_of_dvd hD hdtD
      have hddt := Nat.le_mul_of_pos_right d ht.pos
      have hdtodd := hd.mul ht
      have hmain : d*t*r=2^E+u := by rw [Nat.mul_assoc,← hfac,heq]
      rcases hr with rfl | ⟨hrp,hBr⟩
      · rw [Nat.mul_one] at hmain
        have := Nat.lt_two_pow_self (n:=E)
        omega
      · have hwide : W+2*D<E := by
          by_contra! hn
          exact hgap E u (d*t) r hWE hn hu (hud.trans (hddt.trans hdtle)) hdtodd.pos hdtle hrp hmain
        have hdvd : r ∣ D*primesProduct T := (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (hfac ▸ dvd_mul_left r t) d) (demands T)).trans hbudget
        have hprod := (hrp.dvd_mul.mp hdvd).resolve_left (fun h => hBr.not_ge (hsD r hrp h))
        have hrT := prime_mem_of_dvd (fun q h => ⟨(hT q h).1,by have := (hT q h).2; omega⟩) hrp hprod
        have hrOdd := hrp.odd_of_ne_two (by omega)
        obtain ⟨j,w,hj,hw,hwle,hnex⟩ :=
          next_exponent hu.pos (hud.trans hddt) hdtle hdtodd hrOdd (by omega) hmain
        have hdemOdd : Odd (demand r) := Nat.not_even_iff_odd.mp (fun h =>
          (Nat.not_dvd_ordCompl Nat.prime_two (show 1+r ≠ 0 by omega)) (even_iff_two_dvd.mp h))
        have hdprod : demand r*demands (T.erase r)=demands T := Finset.mul_prod_erase T demand hrT
        have hpProd : r*primesProduct (T.erase r)=primesProduct T := Finset.mul_prod_erase T (fun z : ℕ => z) hrT
        have hnext : (d*t)*demand r*demands (T.erase r) ∣ D*primesProduct (T.erase r) := by
          apply Nat.dvd_of_mul_dvd_mul_left hrp.pos
          rw [show r*(d*t*demand r*demands (T.erase r))=d*H*(demand r*demands (T.erase r)) by rw [hfac]; ac_rfl,
            show r*(D*primesProduct (T.erase r))=D*(r*primesProduct (T.erase r)) by ac_rfl,hdprod,hpProd]
          exact hbudget
        have bound := ih _ (Finset.erase_ssubset hrT) (fun q h => hT q (Finset.mem_of_mem_erase h))
          (fun q h => hthin q (Finset.mem_of_mem_erase h)) hdtodd hdemOdd hw hwle hsdt (hthin r hrT) hnex hnext
        omega

  let smallProduct (B : ℕ) : ℕ := ∏ p ∈ (Finset.range (B+1)).filter Nat.Prime, p

  have smallProduct_pos (B : ℕ) : 0 < smallProduct B :=
    Finset.prod_pos (fun _ hp => (Finset.mem_filter.mp hp).2.pos)

  have smallProduct_smooth (B : ℕ) : Smooth B (smallProduct B) := by
    intro p hp hd
    obtain ⟨r,hr,hpr⟩ := (hp.prime.dvd_finsetProd_iff (fun x : ℕ => x)).mp hd
    have h := Finset.mem_filter.mp hr
    have he := (h.2.dvd_iff_eq hp.ne_one).mp hpr
    have hrB := Finset.mem_range.mp h.1
    omega


  have fixed_core_seed_bound {B c d₀ : ℕ} (hB : 2≤B) (hc : 0<c) (hcB : Smooth B c)
      (hd : Odd d₀) (hdB : Smooth B d₀) :
      ∃ W : ℕ, ∀ (S : Finset ℕ) (m E : ℕ), primeSupport S →
        m*demands S ∣ c*primesProduct S → Odd m → d₀*m=2^E+1 →
        OneLarge B m → (∀ q ∈ S, B<q → OneLarge B (demand q)) → E<W := by
    let D := d₀*(c*smallProduct B)
    have hD : 0<D := Nat.mul_pos hd.pos (Nat.mul_pos hc (smallProduct_pos B))
    have hsD : Smooth B D := smooth_mul hdB (smooth_mul hcB (smallProduct_smooth B))
    obtain ⟨W,hW,hgap⟩ := prime_free_interval D
    refine ⟨W,?_⟩
    intro S m E hS hbal hm heq hone hsh
    let T := S.filter (fun q => B<q)
    let U := S.filter (fun q => ¬ B<q)
    have ht (q : ℕ) (hq : q∈T) : q∈S ∧ B<q := Finset.mem_filter.mp hq
    have hTU : primesProduct T*primesProduct U=primesProduct S :=
      Finset.prod_filter_mul_prod_filter_not S (fun q : ℕ => B<q) (fun q : ℕ => q)
    have hsub : U ⊆ (Finset.range (B+1)).filter Nat.Prime := by
      intro q hq
      obtain ⟨hqS,hqB⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),(hS q hqS).1⟩
    have hdiv : primesProduct U ∣ smallProduct B := Finset.prod_dvd_prod_of_subset U _ _ hsub
    have hu : primesProduct S ∣ smallProduct B*primesProduct T := by
      rw [← hTU,Nat.mul_comm (smallProduct B)]
      exact Nat.mul_dvd_mul_left _ hdiv
    have hleft : demands T ∣ demands S :=
      Finset.prod_dvd_prod_of_subset T S demand (fun q hq => (ht q hq).1)
    have hbudget : d₀*m*demands T ∣ D*primesProduct T := by
      dsimp [D]
      rw [Nat.mul_assoc d₀,Nat.mul_assoc d₀,Nat.mul_assoc c]
      exact Nat.mul_dvd_mul_left d₀ (((Nat.mul_dvd_mul_left m hleft).trans hbal).trans (Nat.mul_dvd_mul_left c hu))
    exact chain_bound hB hD hsD hW hgap T (fun q h => ⟨(hS q (ht q h).1).1,(ht q h).2⟩)
      (fun q h => hsh q (ht q h).1 (ht q h).2) hd hm odd_one hd.pos hdB hone heq hbudget
  have ofPairs {z : ℕ} (h : ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ z → min p r ≤ B) :
      OneLarge B z := by
    by_cases hex : ∃ r : ℕ, r.Prime ∧ B<r ∧ r ∣ z
    · obtain ⟨r,hr,hBr,t,rfl⟩ := hex
      refine ⟨t,r,Nat.mul_comm _ _,?_,.inr ⟨hr,hBr⟩⟩
      intro p hp hpt
      have hv := h r p hr hp (Nat.mul_dvd_mul_left r hpt)
      omega
    · exact ⟨z,1,by simp,fun p hp hd => by
        by_contra! hB
        exact hex ⟨p,hp,hB,hd⟩,.inl rfl⟩
  have h1 : Smooth B 1 := fun p hp h => False.elim (hp.not_dvd_one h)
  obtain ⟨W,hW⟩ := fixed_core_seed_bound (d₀:=1) hB hc hcB odd_one h1
  refine ⟨W,?_⟩
  intro S E hE hS hdiv hseed hsh
  apply hW S _ E hS hdiv ((even_two.pow_of_ne_zero hE.ne').add_odd odd_one) (by simp) (ofPairs hseed)
  exact fun q hq _ => ofPairs (fun p r hp hr hpr =>
    hsh q hq p r hp hr (hpr.trans (Nat.ordCompl_dvd (1+q) 2)))

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2.H2 := by
  intro h₁ h₂ c hc hp
  obtain ⟨B₁,hseed⟩ := h₁ c hc hp
  obtain ⟨B₂,hshift⟩ := h₂ c hc hp
  let B := max (max c 2) (max B₁ B₂)
  have hB : 2≤B := by dsimp [B]; omega
  have hcB : ∀ p : ℕ, p.Prime → p ∣ c → p≤B := fun p _ hd =>
    (Nat.le_of_dvd hc.pos hd).trans (by dsimp [B]; omega)
  obtain ⟨W,hW⟩ := bound_from_prime_pairs hB hc.pos hcB
  apply (Set.finite_Iio W).subset
  intro a ha
  obtain ⟨ha,S,hs,hsub,hpr,heq⟩ := ha
  have har : 0<a := by omega
  have h2d : 2 ∣ 2^a*c := dvd_mul_of_dvd_left (dvd_pow_self 2 har.ne') _
  apply hW S a har (fun q hq => ⟨(hpr q hq).1,fun h => (hpr q hq).2 (h ▸ h2d)⟩)
    (seed_divisibility har hc S heq)
  · intro p r hpp hrr hd
    exact (hseed a S ha hs hsub hpr heq p r hpp hrr hd).trans (by dsimp [B]; omega)
  · intro q hq p r hpp hrr hd
    exact (hshift a S ha hs hsub hpr heq q hq p r hpp hrr hd).trans (by dsimp [B]; omega)

end OMA.R_Erdos1052_erdos_1052_R2_H2_R2
