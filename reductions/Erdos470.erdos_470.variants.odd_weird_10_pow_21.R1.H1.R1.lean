import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1
import Mathlib

/-!
For a primitive abundant number, write the excess as the sum of its proper divisors minus
the number itself. Representing the excess gives a pseudoperfect certificate by complementation.
For a coprime prime power extension of a deficient cofactor, translate a central interval of
cofactor sums using disjoint layers of divisors. For repeated primes, the deficiency of the
preceding level bounds the excess even when the exponent is large.
-/

-- This extends the divisor-sum criterion in PR 6970 and the primitive reduction in PR 2777.

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1

open Finset ArithmeticFunction

namespace OddWeirdFinalPrime

/-- The three sufficient alternatives are the ordinary gap lift, four central intervals
translated by 0, q, u, u+q (where u=P+D), and direct base representation of E. -/
theorem final_prime_alternatives {P D q L g E : ℤ}
    (hg : 1 ≤ g) (hL : 1 ≤ L) (hD : 2 ≤ D) (hq : 3 ≤ q)
    (big : (2*g+1)*(2*L+8*g+8) ≤ P)
    (excess : E = 2*P-D*(q-1)) (low : L ≤ E) :
    (g*q ≤ P-2*L+1 ∧ D+2*L-1 ≤ q*P) ∨
    (q ≤ P-2*L+1 ∧ D+2*L-1 ≤ q ∧ E ≤ 2*P+D+q-L) ∨
    (L ≤ E ∧ E ≤ P-L) := by
  have gL : 0 ≤ g*L := mul_nonneg (by omega) (by omega)
  have gg : 0 ≤ g*g := mul_self_nonneg g
  have g1L : 0 ≤ (g-1)*L := mul_nonneg (by omega) (by omega)
  have pbound : 5*L ≤ P := by nlinarith only [big,hg,hL,gg,g1L]
  have dpos : 0 ≤ D := by omega
  have dlt : D < P := by nlinarith only [excess,low,hL,mul_nonneg (show 0 ≤ q-3 by omega) dpos]
  by_cases small : g*q ≤ P-2*L+1
  · left
    refine ⟨small,?_⟩
    have t := mul_le_mul_of_nonneg_right hq (show 0 ≤ P by omega)
    nlinarith only [t,dlt,pbound,hL]
  · have dcap : D < 8*g := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ q-1 by omega)
      have w := mul_nonneg (show 0 ≤ g by omega) (show 0 ≤ q-2 by omega)
      nlinarith only [small,k,w,excess,low,pbound,hL]
    have bigq : 2*L+8*g+8 < q := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0 ≤ g by omega)
      nlinarith only [k,small,big,gg,gL,hg]
    by_cases overlap : q ≤ P-2*L+1
    · right; left
      have h := mul_nonneg dpos (show 0 ≤ q-1 by omega)
      exact ⟨overlap,by omega,by linarith only [excess,h,hD,bigq,hg,hL]⟩
    · right; right
      have k := mul_le_mul_of_nonneg_left hD (show 0 ≤ q-1 by omega)
      exact ⟨low,by nlinarith only [k,excess,overlap,pbound]⟩

/-- Four translated intervals [L,P-L]+j have no internal gap for j=0,q,P+D,P+D+q. -/
theorem four_interval_join {P D q L A : ℤ} (w : q ≤ P-2*L+1) (v : D+2*L-1 ≤ q)
    (lo : L ≤ A) (hi : A ≤ 2*P+D+q-L) :
    (L ≤ A ∧ A ≤ P-L) ∨ (L ≤ A-q ∧ A-q ≤ P-L) ∨
    (L ≤ A-(P+D) ∧ A-(P+D) ≤ P-L) ∨
    (L ≤ A-(P+D+q) ∧ A-(P+D+q) ≤ P-L) := by omega

end OddWeirdFinalPrime


namespace OddWeirdRepeatedFinal

/-- For deficient b with positive proper-divisor sum P and deficiency D,
a primitive abundant extension by q^a with a≥2 needs D(q−2)<2P<D(q−1).
In particular q fits below the central interval width and the deficiency is at least three. -/
theorem repeated_bounds {P D q L : ℤ} (hD : 0<D) (hq : 3≤q)
    (large : 6*L≤P) (low : D*(q-2)<2*P) (high : 2*P<D*(q-1))
    (divone : ¬ D ∣ 2*P) :
    3≤D ∧ q≤P-2*L+1 := by
  have three : 3≤D := by
    by_contra! bad
    interval_cases D <;> simp at divone
  refine ⟨three,?_⟩
  have a := mul_le_mul_of_nonneg_right three (show 0≤q-2 by omega)
  omega

/-- No multiple of D lies strictly between two consecutive multiples of positive D. -/
theorem nondivisor {P D q : ℤ} (hD : 0<D)
    (low : D*(q-2)<2*P) (high : 2*P<D*(q-1)) : ¬D ∣ 2*P := by
  rintro ⟨x,h⟩
  rw [h] at low high
  have a := (mul_lt_mul_iff_right₀ hD).mp low
  have b := (mul_lt_mul_iff_right₀ hD).mp high
  omega

/-- Both alternatives give a divisor-sum cover from just the first two q layers. -/
theorem repeated_alternatives {P D q L g E : ℤ} (hg : 1≤g) (hL : 1≤L)
    (hD : 0<D) (hq : 3≤q) (big : (2*g+1)*(2*L+8*g+8)≤P)
    (low : D*(q-2)<2*P) (high : 2*P<D*(q-1)) (excess : E≤2*P+D-q) :
    (g*q≤P-2*L+1 ∧ D+2*L-1≤q*P ∧ E≤2*P+D+q*P-L) ∨
    (q≤P-2*L+1 ∧ D+2*L-1≤q ∧ E≤2*P+D+q-L) := by
  have gL := mul_nonneg (show 0≤g-1 by omega) (show 0≤L by omega)
  have gg := mul_self_nonneg g
  have pl : 6*L≤P := by nlinarith only [big,hg,gL,gg]
  have pd : D<2*P := by nlinarith only [low,mul_nonneg (show 0≤D by omega) (show 0≤q-3 by omega)]
  obtain ⟨_,qw⟩ := repeated_bounds hD hq pl low high (nondivisor hD low high)
  by_cases small : g*q≤P-2*L+1
  · left
    have covers := mul_le_mul_of_nonneg_right hq (show 0≤P by omega)
    exact ⟨small, by omega, by omega⟩
  · right
    have largeQ : 2*L+8*g+8<q := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_left h (show 0≤g by omega)
      nlinarith only [k,small,big,gg,gL,hg,hL]
    have dcap : D<8*g := by
      by_contra! h
      have k := mul_le_mul_of_nonneg_right h (show 0≤q-2 by omega)
      have w := mul_nonneg (show 0≤g by omega) (show 0≤q-4 by omega)
      nlinarith only [k,low,small,pl,hL,w]
    exact ⟨qw,by omega,by omega⟩


/-- For b coprime to q put P=σ(b)−b, D=b−P, and E(j)=σ(b*q^j)−2*b*q^j.
Multiplicativity gives the displayed recurrence. Its closed form supplies both
strict bounds and the upper bound used in the interval certificate. -/
theorem repeat_from_excess {P D q : ℤ} (hq : 0 < q-1) (hs : 0 < 2*P+D)
    (E : ℕ → ℤ) (base : E 0 = -D)
    (next : ∀ j, E (j+1) = q*E j+(2*P+D))
    (j : ℕ) (firstDef : E 1 < 0) (previousDef : E j < 0) (abundant : 0 < E (j+1)) :
    D*(q-2)<2*P ∧ 2*P<D*(q-1) ∧ E (j+1)≤2*P+D-q := by
  have closed (t : ℕ) : (q-1)*E t = q^t*(2*P-D*(q-2))-(2*P+D) := by
    induction t with
    | zero => rw [base,pow_zero]; ring
    | succ t ih =>
      rw [next,pow_succ]
      calc
        _ = q*((q-1)*E t)+(q-1)*(2*P+D) := by ring
        _ = _ := by rw [ih]; ring
  have c := closed (j+1)
  have prodPos := mul_pos hq abundant
  have pos : 0 < 2*P-D*(q-2) := by
    by_contra! h
    have x := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (show 0 ≤ q by omega) (j+1)) h
    omega
  have one := next 0
  rw [base] at one
  have qNonneg : 0≤q := by omega
  have neg := mul_le_mul_of_nonneg_left (show E j ≤ -1 by omega) qNonneg
  refine ⟨by omega,?_,?_⟩
  · nlinarith only [firstDef,one]
  · rw [next]; linarith only [neg]

end OddWeirdRepeatedFinal


namespace OddWeirdPowerLayers

/-- The directed gap bound on A means each integer k before the largest index
is within g-1 above an index in A. Each index translates an interval by r*i. -/
theorem index_for_translate {A : Set ℤ} {T L H g r x : ℤ}
    (hr : 0<r) (wide : r*g≤H-L+1) (last : T∈A)
    (gap : ∀ k : ℤ,0≤k → k<T → ∃ i ∈ A, k - g < i ∧ i ≤ k)
    (lo : L≤x) (hi : x≤H+r*T) :
    ∃ i ∈ A,  L≤x-r*i ∧ x-r*i≤H := by
  by_cases finished : L+r*T≤x
  · exact ⟨T,last,by omega,by omega⟩
  let k := (x-L)/r
  have kp : k<T := Int.ediv_lt_of_lt_mul hr (by rw [mul_comm T r]; omega)
  obtain ⟨i,mem,lower,upper⟩ := gap k (Int.ediv_nonneg (by omega) (by omega)) kp
  have decomp := Int.emod_add_mul_ediv (x-L) r
  change (x-L)%r + r*k = x-L at decomp
  have remLo := Int.emod_nonneg (x-L) (by omega : r≠0)
  have remHi := Int.emod_lt_of_pos (x-L) hr
  have left := mul_le_mul_of_nonneg_left upper (le_of_lt hr)
  have right := mul_le_mul_of_nonneg_left (show k-g+1 ≤ i by omega) (le_of_lt hr)
  rw [mul_add,mul_sub,mul_one] at right
  exact ⟨i,mem,by omega,by omega⟩

/-- Suppose A is the proper-divisor sums of b*r^j, B those of b, and C those of
b*r^(j+1). The two layer hypotheses follow by disjointness when r is prime and
coprime to b. All divisors of b occur unscaled, and r multiplies the proper
divisors of the previous level. -/
theorem middle_next {A B C : Set ℤ} {T P b L g r : ℤ}
    (hr : 0<r) (wide : r*g≤P-2*L+1) (overlap : b+2*L≤P+r*T+1)
    (endA : T∈A) (gap : ∀ k : ℤ,0≤k → k<T → ∃ i ∈ A, k - g < i ∧ i ≤ k)
    (central : ∀ y : ℤ,L≤y → y≤P-L → y∈B)
    (layers : ∀ i ∈ A, ∀ y∈B,y+r*i∈C ∧ b+y+r*i∈C) :
    ∀ x : ℤ,L≤x → x≤b+P+r*T-L → x∈C := by
  intro x low high
  by_cases first : x≤P-L+r*T
  · obtain ⟨i,hi,h,k⟩ := index_for_translate hr (show r*g≤(P-L)-L+1 by omega) endA gap low first
    have represented := (layers i hi _ (central _ h k)).1
    convert represented using 1
    ring
  · obtain ⟨i,hi,h,k⟩ := index_for_translate (x:=x-b) hr (show r*g≤(P-L)-L+1 by omega) endA gap
      (show L≤x-b by omega) (show x-b≤(P-L)+r*T by omega)
    have represented := (layers i hi _ (central _ h k)).2
    convert represented using 1
    ring

end OddWeirdPowerLayers

/-- A subset of proper divisors representing the excess leaves a subset summing to m. -/
theorem pseudoperfect_of_excess {m : ℕ} (pos : 0 < m) {s : Finset ℕ}
    (subset : s ⊆ m.properDivisors)
    (sum : (∑ d ∈ s, (d : ℤ)) = (sigma 1 m : ℤ) - 2 * (m : ℤ)) : m.Pseudoperfect := by
  classical
  have total : (sigma 1 m : ℤ) = (∑ d ∈ m.properDivisors, (d : ℤ)) + m := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp
  have rest := sum_sdiff subset (f := fun x : ℕ => (x : ℤ))
  refine ⟨pos, m.properDivisors \ s, sdiff_subset, Int.ofNat_inj.mp ?_⟩
  push_cast
  linarith only [sum,total,rest]

set_option maxHeartbeats 2400000 in
/-- A dense middle interval and a directed gap bound for the proper-divisor sums of b
certify every indicated prime-power extension, with no bound on its size or prime count. -/
theorem certified_prime_power {b q j : ℕ} (bpos : 1 < b) (hq : q.Prime)
    (coprime : b.Coprime q) (q3 : 3 ≤ q)
    (primitive : ∀ d ∈ (b*q^(j+1)).properDivisors, d.Deficient)
    (L g : ℤ) (lpos : 1 ≤ L) (gpos : 1 ≤ g)
    (high : L ≤ (sigma 1 (b*q^(j+1)) : ℤ) - 2 * (b*q^(j+1) : ℕ)) :
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    (2*g+1)*(2*L+8*g+8) ≤ P → (j = 0 → 2 ≤ (b : ℤ) - P) →
    (∀ y : ℤ, L ≤ y → y ≤ P-L → R y) →
    (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k-g < i ∧ i ≤ k) →
    ¬(b*q^(j+1)).Weird := by
  classical
  let represented (n : ℕ) (x : ℤ) : Prop :=
    ∃ s : Finset ℕ, s ⊆ n.properDivisors ∧ (∑ d ∈ s, (d : ℤ)) = x
  let properTotal (n : ℕ) : ℤ := ∑ d ∈ n.properDivisors, (d : ℤ)
  let excess (n : ℕ) : ℤ := (sigma 1 n : ℕ) - 2*(n : ℤ)

  -- Unscaled divisors of b and q-scaled proper divisors of a preceding level are disjoint.
  have combine {b m q : ℕ} (hm : 0 < m) (bm : b ∣ m) (hn : ¬q ∣ b)
      (hq : 1 < q) {s t : Finset ℕ} (hs : s ⊆ b.divisors) (ht : t ⊆ m.properDivisors) :
      represented (q*m) ((∑ d ∈ s, (d : ℤ)) + q * ∑ d ∈ t, (d : ℤ)) := by
    let f (x : ℕ) := q*x
    have positive : 0 < q := by omega
    have inj : Function.Injective f := fun x y eq => Nat.eq_of_mul_eq_mul_left positive eq
    have subset : s ⊆ (q*m).properDivisors := by
      intro x hx
      have d := Nat.dvd_of_mem_divisors (hs hx)
      have dm := d.trans bm
      refine Nat.mem_properDivisors.mpr ⟨dm.trans (dvd_mul_left _ _),?_⟩
      exact lt_of_le_of_lt (Nat.le_of_dvd hm dm) (by simpa using Nat.mul_lt_mul_of_pos_right hq hm)
    have scaled : t.image f ⊆ (q*m).properDivisors := by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      obtain ⟨div,lt⟩ := Nat.mem_properDivisors.mp (ht hz)
      exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_left q div,Nat.mul_lt_mul_of_pos_left lt positive⟩
    have separate : Disjoint s (t.image f) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx'
      exact hn ((dvd_mul_right q z).trans (Nat.dvd_of_mem_divisors (hs hx)))
    refine ⟨s ∪ t.image f,Finset.union_subset subset scaled,?_⟩
    rw [sum_union separate,sum_image (fun x _ y _ eq => inj eq),Finset.mul_sum]
    simp [f]

  -- At each level the unscaled set can also include b itself.
  have layers {b m q : ℕ} (hm : 0 < m) (bm : b ∣ m) (hn : ¬q ∣ b)
      (hq : 1<q) {i y : ℤ} (hi : represented m i) (hy : represented b y) :
      represented (q*m) (y+q*i) ∧ represented (q*m) (b+y+q*i) := by
    obtain ⟨s,hs,rfl⟩ := hy
    obtain ⟨t,ht,rfl⟩ := hi
    have hb : b≠0 := by
      intro z
      subst b
      exact hm.ne' (by simpa using bm)
    have full : insert b s ⊆ b.divisors := by
      rw [←Nat.insert_self_properDivisors hb]
      exact Finset.insert_subset_insert _ hs
    constructor
    · exact combine hm bm hn hq (hs.trans Nat.properDivisors_subset_divisors) ht
    · have nb : b ∉ s := fun h => Nat.self_notMem_properDivisors (hs h)
      simpa [sum_insert nb] using combine hm bm hn hq full ht
  have complement {n : ℕ} (hn : 0<n) {e : ℤ} (rep : represented n e)
      (total : (∑ x ∈ n.properDivisors, (x : ℤ)) = n+e) : ¬n.Weird := by
    obtain ⟨s,hs,h⟩ := rep
    rintro ⟨_,no⟩
    apply no (pseudoperfect_of_excess hn hs ?_)
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    push_cast
    linarith only [h,total]
  have sigma_split (n : ℕ) : (sigma 1 n : ℤ) = properTotal n + n := by
    rw [ArithmeticFunction.sigma_one_apply,Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp [properTotal]

  -- Multiplicativity gives a recurrence for the excess along a prime power.
  have excess_step {b q : ℕ} (prime : q.Prime) (cop : b.Coprime q) (j : ℕ) :
      excess (b*q^(j+1)) = q*excess (b*q^j)+(sigma 1 b : ℕ) := by
    have recurEq : sigma 1 (b*q^(j+1)) = q*sigma 1 (b*q^j)+sigma 1 b := by
      rw [isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right (j+1)),
          isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right j),
          sigma_one_apply_prime_pow prime,sigma_one_apply_prime_pow prime,geom_sum_succ]
      ring
    dsimp [excess]
    rw [recurEq]
    push_cast
    ring

  -- The deficient preceding level bounds the excess of a repeated-prime extension.
  have not_weird_repeated_final {b q j : ℕ} (basePos : 1 < b) (prime : q.Prime)
      (cop : b.Coprime q) (q3 : 3≤q) (L g : ℤ) (gpos : 1≤g) (lpos : 1≤L)
      (deficient : properTotal b < b)
      (large : (2*g+1)*(2*L+8*g+8)≤properTotal b)
      (middle : ∀ y : ℤ,L≤y → y≤properTotal b-L → represented b y)
      (gap : ∀ k : ℤ,0≤k → k<properTotal b → ∃ i : ℤ, represented b i ∧ k-g < i ∧ i ≤ k)
      (firstDef : excess (b*q)<0) (prevDef : excess (b*q^j)<0)
      (high : L≤excess (b*q^(j+1))) : ¬(b*q^(j+1)).Weird := by
    let P := properTotal b
    let D : ℤ := b-P
    let E (t : ℕ) := excess (b*q^t)
    have bpos : 0<b := by omega
    have qpos : 0<q := prime.pos
    have hq : (3 : ℤ)≤q := by exact_mod_cast q3
    have sig : (sigma 1 b : ℤ)=2*P+D := by rw [sigma_split]; dsimp [P,D]; ring
    have sPos : 0<2*P+D := by rw [←sig]; exact_mod_cast (sigma_pos_iff.mpr bpos : 0<sigma 1 b)
    have dPos : 0<D := by dsimp [D,P]; omega
    have recurEq (t : ℕ) : E (t+1)=(q : ℤ)*E t+(2*P+D) := by rw [←sig]; exact excess_step prime cop t
    have e0 : E 0 = -D := by simp only [E,pow_zero,mul_one,excess,sig]; dsimp [D]; ring
    have one : E 1<0 := by simpa [E] using firstDef
    obtain ⟨l,h,e⟩ := OddWeirdRepeatedFinal.repeat_from_excess (q:=(q:ℤ)) (by omega) sPos
      E e0 recurEq j one prevDef (lt_of_lt_of_le (by omega : 0<L) high)
    have alt := OddWeirdRepeatedFinal.repeated_alternatives (P:=P) (D:=D) (E:=E (j+1)) gpos lpos dPos hq large l h e
    have total : represented b P := ⟨_,fun _ h => h,rfl⟩
    have zero : represented b 0 := ⟨∅,by simp,by simp⟩
    have unit : represented b 1 := ⟨{1},by simpa using Nat.one_mem_properDivisors_iff_one_lt.mpr basePos,by simp⟩
    have translate (i y : ℤ) (hi : represented b i) (hy : represented b y) :
        represented (b*q^(j+1)) (y+q*i) ∧ represented (b*q^(j+1)) (b+y+q*i) := by
      have divis : b ∣ b*q^j := dvd_mul_right _ _
      have pos : 0<b*q^j := by positivity
      obtain ⟨t,sub,ht⟩ := hi
      have inclusion : represented (b*q^j) i := by
        refine ⟨t,fun d hd => ?_,ht⟩
        obtain ⟨dvd,lt⟩ := Nat.mem_properDivisors.mp (sub hd)
        exact Nat.mem_properDivisors.mpr ⟨dvd.trans divis,lt_of_lt_of_le lt (Nat.le_of_dvd pos divis)⟩
      have holds := layers pos divis (prime.coprime_iff_not_dvd.mp cop.symm) prime.one_lt inclusion hy
      convert holds using 2 <;> ring
    have can : represented (b*q^(j+1)) (E (j+1)) := by
      rcases alt with ⟨wide,join,cap⟩|⟨wide,join,cap⟩
      · exact OddWeirdPowerLayers.middle_next (A:=fun i => represented b i) (B:=fun y => represented b y)
          (C:=fun z => represented (b*q^(j+1)) z) (P:=P) (T:=P) (b:=(b:ℤ))
          (by omega : (0:ℤ)<q) (by simpa only [mul_comm (q:ℤ) g] using wide) (by change (b:ℤ)-P+2*L-1 ≤ q*P at join; omega) total gap middle (fun i hi y hy => translate i y hi hy)
          _ high (by change E (j+1) ≤ 2*P+((b:ℤ)-P)+q*P-L at cap; omega)
      · have bEq : P+D=(b:ℤ) := by dsimp [D]; ring
        rcases OddWeirdFinalPrime.four_interval_join wide join high cap with h|h|h|h
        · simpa using (translate 0 _ zero (middle _ h.1 h.2)).1
        · simpa using (translate 1 _ unit (middle _ h.1 h.2)).1
        · rw [bEq] at h
          simpa using (translate 0 _ zero (middle _ h.1 h.2)).2
        · rw [bEq] at h
          convert (translate 1 _ unit (middle _ h.1 h.2)).2 using 1
          ring
    apply complement (by positivity) can
    change properTotal (b*q^(j+1)) = _ + excess (b*q^(j+1))
    dsimp only [excess]
    rw [sigma_split]
    ring

  -- For a simple final prime the excess is affine in q.
  have not_weird_simple_final {b q : ℕ} (basePos : 1 < b) (prime : q.Prime)
      (cop : b.Coprime q) (q3 : 3≤q) (L g : ℤ) (gpos : 1≤g) (lpos : 1≤L)
      (deficient : 2 ≤ (b:ℤ) - properTotal b)
      (large : (2*g+1)*(2*L+8*g+8)≤properTotal b)
      (middle : ∀ y : ℤ,L≤y → y≤properTotal b-L → represented b y)
      (gap : ∀ k : ℤ,0≤k → k<properTotal b → ∃ i : ℤ, represented b i ∧ k-g < i ∧ i ≤ k)
      (high : L≤excess (b*q)) : ¬(b*q).Weird := by
    let P := properTotal b
    let D : ℤ := b-P
    let E := excess (b*q)
    have bpos : 0<b := by omega
    have qpos : 0<q := prime.pos
    have hq : (3 : ℤ)≤q := by exact_mod_cast q3
    have formula : E=2*P-D*(q-1) := by
      have first := excess_step prime cop 0
      simp only [pow_zero,pow_one,mul_one,zero_add] at first
      dsimp only [E,P,D]
      rw [first]
      unfold excess
      rw [sigma_split b]
      ring
    have cases' := OddWeirdFinalPrime.final_prime_alternatives gpos lpos deficient hq large formula high
    have total : represented b P := ⟨_,fun _ h => h,rfl⟩
    have zero : represented b 0 := ⟨∅,by simp,by simp⟩
    have unit : represented b 1 := ⟨{1},by simpa using Nat.one_mem_properDivisors_iff_one_lt.mpr basePos,by simp⟩
    have translate (i y : ℤ) (hi : represented b i) (hy : represented b y) :
        represented (b*q) (y+q*i) ∧ represented (b*q) (b+y+q*i) := by
      simpa only [mul_comm q b] using layers bpos (dvd_refl _) (prime.coprime_iff_not_dvd.mp cop.symm) prime.one_lt hi hy
    have can : represented (b*q) E := by
      rcases cases' with ⟨wide,join⟩|⟨wide,join,cap⟩|basic
      · have gb := mul_nonneg (show 0≤g-1 by omega) (show 0≤L by omega)
        have gg := mul_self_nonneg g
        have pL : L≤P := by change _≤P at large; nlinarith only [large,gpos,lpos,gb,gg]
        have qP := mul_le_mul_of_nonneg_right hq (show 0≤P by omega)
        have prod := mul_nonneg (show 0≤D by exact le_trans (by decide : (0:ℤ)≤2) deficient) (show 0≤(q:ℤ)-1 by omega)
        exact OddWeirdPowerLayers.middle_next (A:=fun i => represented b i) (B:=fun y => represented b y)
          (C:=fun z => represented (b*q) z) (P:=P) (T:=P) (b:=(b:ℤ)) (by omega : (0:ℤ)<q)
          (by simpa only [mul_comm (q:ℤ) g] using wide)
          (by change (b:ℤ)-P+2*L-1 ≤ q*P at join; omega) total gap middle (fun i hi y hy => translate i y hi hy)
          _ high (by dsimp only [D] at formula prod; omega)
      · have eq : P+D=(b:ℤ) := by dsimp [D]; ring
        rcases OddWeirdFinalPrime.four_interval_join wide join high cap with h|h|h|h
        · simpa using (translate 0 _ zero (middle _ h.1 h.2)).1
        · simpa using (translate 1 _ unit (middle _ h.1 h.2)).1
        · rw [eq] at h
          simpa using (translate 0 _ zero (middle _ h.1 h.2)).2
        · rw [eq] at h
          convert (translate 1 _ unit (middle _ h.1 h.2)).2 using 1
          ring
      · simpa using (translate 0 _ zero (middle _ basic.1 basic.2)).1
    apply complement (by positivity) can
    change properTotal (b*q) = _ + excess (b*q)
    dsimp only [excess]
    rw [sigma_split]
    ring

  intro P R large simple middle gap weird
  change (2*g+1)*(2*L+8*g+8) ≤ properTotal b at large
  change L ≤ excess (b*q^(j+1)) at high
  by_cases zero : j = 0
  · subst j
    simp only [zero_add, pow_one] at weird high
    exact not_weird_simple_final bpos hq coprime q3 L g gpos lpos
      (simple rfl) large middle gap high weird
  · have earlier (k : ℕ) (hk : k < j+1) : properTotal (b*q^k) < (b*q^k : ℕ) := by
      have mem : b*q^k ∈ (b*q^(j+1)).properDivisors := Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_left b (pow_dvd_pow q hk.le),
         Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hq.one_lt hk) (by omega)⟩
      have defic := primitive _ mem
      change ∑ d ∈ (b*q^k).properDivisors, d < b*q^k at defic
      dsimp only [properTotal]
      rw [← Nat.cast_sum]
      exact_mod_cast defic
    have earlierEx (k : ℕ) (hk : k < j+1) : excess (b*q^k) < 0 := by
      dsimp only [excess]
      rw [sigma_split]
      linarith only [earlier k hk]
    have defBase : properTotal b < b := by simpa using earlier 0 (by omega)
    have defFirst : excess (b*q) < 0 := by simpa using earlierEx 1 (by omega)
    exact not_weird_repeated_final bpos hq coprime q3 L g gpos lpos defBase
      large middle gap defFirst (earlierEx j (by omega)) high weird


/-- Every abundant multiple of three has a largest prime divisor, whose full prime power
leaves a nontrivial coprime cofactor. -/
theorem largest_prime_power {n : ℕ} (ab : n.Abundant) (three : 3 ∣ n) :
    ∃ b q j : ℕ, n = b*q^(j+1) ∧ 1 < b ∧ q.Prime ∧ 3 ≤ q ∧ b.Coprime q ∧
      ∀ p ∈ b.primeFactors, p < q := by
  have h3 : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide,three,ab.pos.ne'⟩
  have nonempty : n.primeFactors.Nonempty := ⟨3,h3⟩
  let q := n.primeFactors.max' nonempty
  have mem : q ∈ n.primeFactors := Finset.max'_mem _ _
  have hq := (Nat.mem_primeFactors.mp mem).1
  have exppos : n.factorization q ≠ 0 := by
    rwa [← Finsupp.mem_support_iff, Nat.support_factorization]
  obtain ⟨j,ej⟩ := Nat.exists_eq_succ_of_ne_zero exppos
  have ej' : n.factorization q = j+1 := ej
  let b := n / q^(n.factorization q)
  have H : n = b*q^(j+1) := by
    rw [← ej', mul_comm]
    exact (Nat.ordProj_mul_ordCompl_eq_self n q).symm
  have bp : 0 < b := Nat.ordCompl_pos q ab.pos.ne'
  have cp : b.Coprime q := (Nat.coprime_ordCompl hq ab.pos.ne').symm
  have B : b ≠ 1 := by
    intro one
    have power : n=q^(j+1) := by simpa only [one,one_mul] using H
    rw [power] at ab
    exact Nat.lt_asymm ab hq.deficient_pow
  refine ⟨b,q,j,H,by omega,hq,Finset.le_max' _ _ h3,cp,?_⟩
  intro p hp
  have pd := (Nat.mem_primeFactors.mp hp).2.1
  have pb : b ∣ n := by rw [H]; exact dvd_mul_right _ _
  have pn := Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,pd.trans pb,ab.pos.ne'⟩
  apply lt_of_le_of_ne (Finset.le_max' _ _ pn)
  intro eq
  change p = q at eq
  exact (hq.coprime_iff_not_dvd.mp cp.symm) (eq ▸ pd)

/-- The cofactor divisor sum and twice the cofactor have a common divisor that
also divides the excess of every coprime prime-power extension. -/
theorem gcd_dvd_excess {b q : ℕ} (cop : b.Coprime q) (e : ℕ) :
    (Nat.gcd (sigma 1 b) (2*b) : ℤ) ∣ (sigma 1 (b*q^e) : ℤ) - 2*(b*q^e : ℕ) := by
  apply dvd_sub
  · rw [isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e)]
    exact_mod_cast (Nat.gcd_dvd_left (sigma 1 b) (2*b)).trans (dvd_mul_right _ _)
  · have hh : Nat.gcd (sigma 1 b) (2*b) ∣ (2*b)*q^e :=
      (Nat.gcd_dvd_right (sigma 1 b) (2*b)).trans (dvd_mul_right _ _)
    push_cast
    exact_mod_cast (by simpa only [mul_assoc] using hh : Nat.gcd (sigma 1 b) (2*b) ∣ 2*(b*q^e))

/-- The excess either has a cofactor representation, clears a certified interval margin,
or is a positive multiple of the cofactor gcd below every applicable margin. -/
theorem surviving_excess {b q j : ℕ} (bp : 1 < b) (hq : q.Prime)
    (cop : b.Coprime q) (q3 : 3 ≤ q) (ab : (b*q^(j+1)).Abundant)
    (primitive : ∀ d ∈ (b*q^(j+1)).properDivisors, d.Deficient)
    (no : ¬(b*q^(j+1)).Pseudoperfect) :
    let n := b*q^(j+1)
    let E : ℤ := (sigma 1 n : ℤ) - 2*(n : ℤ)
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    let G : ℤ := Nat.gcd (sigma 1 b) (2*b)
    (¬ ∃ s ⊆ b.divisors, (∑ d ∈ s, (d : ℤ)) = E) ∧
    G ∣ E ∧ 0 < E ∧
    (∀ L g : ℤ, 1 ≤ L → 1 ≤ g → (2*g+1)*(2*L+8*g+8) ≤ P →
      (j = 0 → 2 ≤ (b : ℤ)-P) →
      (∀ y : ℤ, L ≤ y → y ≤ P-L → R y) →
      (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k-g < i ∧ i ≤ k) →
      E < L ∧ G < L) := by
  intro n E P R G
  have pos : 0 < E := by
    have more := Nat.abundant_iff_sum_divisors.mp ab
    change 0 < (sigma 1 (b*q^(j+1)) : ℤ) - 2*(b*q^(j+1) : ℕ)
    rw [ArithmeticFunction.sigma_one_apply]
    exact sub_pos.mpr (by exact_mod_cast more)
  have dg : G ∣ E := gcd_dvd_excess cop (j+1)
  refine ⟨?_,dg,pos,?_⟩
  · rintro ⟨s,sub,sum⟩
    apply no (pseudoperfect_of_excess ab.pos ?_ sum)
    have bigger : b < n := by
      change b < b*q^(j+1)
      have : 1 < q^(j+1) := one_lt_pow₀ hq.one_lt (by omega)
      simpa using Nat.mul_lt_mul_of_pos_left this (by omega : 0<b)
    intro d hd
    have dv := Nat.dvd_of_mem_divisors (sub hd)
    exact Nat.mem_properDivisors.mpr
      ⟨dv.trans (dvd_mul_right _ _),lt_of_le_of_lt (Nat.le_of_dvd (by omega) dv) bigger⟩
  · intro L g lp gp big simple mid gap
    have small : E < L := by
      by_contra! high
      exact certified_prime_power bp hq cop q3 primitive L g lp gp high big simple mid gap ⟨ab,no⟩
    exact ⟨small,lt_of_le_of_lt (Int.le_of_dvd pos dg) small⟩

/-- For a simple largest prime, search for the excess among small distinct proper divisors after the cofactor and central certificates fail. -/
def H1 : Prop :=
  ∀ b q : ℕ, 1 < b → q.Prime → 3 ≤ q → b.Coprime q →
    (∀ p ∈ b.primeFactors, p < q) →
    let n := b*q
    n < 10^21 → Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    let E : ℤ := (sigma 1 n : ℤ) - 2*(n : ℤ)
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    let G : ℤ := Nat.gcd (sigma 1 b) (2*b)
    (¬ ∃ s ⊆ b.divisors, (∑ d ∈ s, (d : ℤ)) = E) →
    G ∣ E → 0 < E →
    (∀ L g : ℤ, 1 ≤ L → 1 ≤ g → (2*g+1)*(2*L+8*g+8) ≤ P →
    2 ≤ (b : ℤ)-P →
      (∀ y : ℤ, L ≤ y → y ≤ P-L → R y) →
      (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k-g < i ∧ i ≤ k) →
      E < L ∧ G < L) →
    ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E), (∑ d ∈ s, (d : ℤ)) = E

/-- For a repeated largest prime, the cofactor certificate works at every exponent without a deficiency-two assumption. -/
def H2 : Prop :=
  ∀ b q j : ℕ, 1 < b → q.Prime → 3 ≤ q → b.Coprime q →
    (∀ p ∈ b.primeFactors, p < q) →
    let n := b*q^(j+2)
    n < 10^21 → Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    let E : ℤ := (sigma 1 n : ℤ) - 2*(n : ℤ)
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    let G : ℤ := Nat.gcd (sigma 1 b) (2*b)
    (¬ ∃ s ⊆ b.divisors, (∑ d ∈ s, (d : ℤ)) = E) →
    G ∣ E → 0 < E →
    (∀ L g : ℤ, 1 ≤ L → 1 ≤ g → (2*g+1)*(2*L+8*g+8) ≤ P →
      (∀ y : ℤ, L ≤ y → y ≤ P-L → R y) →
      (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k-g < i ∧ i ≤ k) →
      E < L ∧ G < L) →
    ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E), (∑ d ∈ s, (d : ℤ)) = E

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1.H1 := by
  intro simple repeated n bound odd ab prim three
  obtain ⟨b,q,j,rfl,bp,hq,q3,cop,largest⟩ := largest_prime_power ab three
  by_contra no
  obtain ⟨missing,divides,positive,bad⟩ := surviving_excess bp hq cop q3 ab prim no
  apply no
  cases j with
  | zero =>
    simp only [zero_add,pow_one] at *
    obtain ⟨s,sub,hs⟩ := simple b q bp hq q3 cop largest bound odd ab prim three
      missing divides positive (fun L g lpos gpos big defic mid gap =>
        bad L g lpos gpos big (fun _ => defic) mid gap)
    exact pseudoperfect_of_excess ab.pos (sub.trans (Finset.filter_subset _ _)) hs
  | succ j =>
    obtain ⟨s,sub,hs⟩ := repeated b q j bp hq q3 cop largest bound odd ab prim three
      missing divides positive (fun L g lpos gpos big mid gap =>
        bad L g lpos gpos big (by intro h; omega) mid gap)
    exact pseudoperfect_of_excess ab.pos (sub.trans (Finset.filter_subset _ _)) hs

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1
