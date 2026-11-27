import FormalConjectures.ErdosProblems.«946»

/-! Heath-Brown's seven-point divisor key and the squarefree almost-prime sieve
for seven linear forms in fixed progressions. See A. Hildebrand, Pacific J.
Math. 129 (1987), 307–319, Lemmas 1 and 2, with Xie's 27-factor bound. -/

namespace OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1
open Finset Filter Real
open scoped ArithmeticFunction.sigma Classical

/-- The quantitative seven-dimensional weighted sieve with prescribed valuations
at distinct primes larger than every slope. Removing the prescribed powers leaves
squarefree integers free of all primes up to any fixed bound. -/
def H1 : Prop := ∀ a q e : Fin 7 → ℕ, StrictMono a → (∀ i, 0 < a i) →
    Function.Injective q → (∀ i, (q i).Prime) → (∀ i j, a i < q j) →
    ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ∃ U : Finset ℕ, x / (log x)^7 ≤ C * U.card ∧ ∀ n ∈ U, 0 < n ∧ (n:ℝ) ≤ x ∧
        let v := fun i => (a i*n+1)/(q i ^ e i)
        (∀ i, q i ^ e i ∣ a i*n+1 ∧ 1 < v i ∧ Squarefree (v i) ∧
          ∀ p ∈ (v i).primeFactors, B < p) ∧ (∑ i, (v i).primeFactors.card) ≤ 27

/-- A seven-point instance of Heath-Brown's key lemma. -/
def H2 : Prop := ∃ a : Fin 7 → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
    ∀ i j, i < j →
      a j - a i = (a i).gcd (a j) ∧
      σ 0 (a i) * σ 0 (a j / (a j - a i)) = σ 0 (a j) * σ 0 (a i / (a j - a i))

section

private lemma distinct_sum (U : Finset ℕ) (pos : ∀ t∈U, 0<t) :
    U.card*(U.card+1)≤2*∑ t∈U,t := by
  induction U using Finset.strongInductionOn
  · rename_i U h
    by_cases ne : U.Nonempty
    · let t := U.max' ne
      have ht : t∈U := max'_mem _ _
      have dom : U⊆Icc 1 t := fun w hw => mem_Icc.mpr ⟨pos w hw,le_max' U w hw⟩
      have card : U.card≤t := (card_le_card dom).trans_eq (by simp)
      have old := h (U.erase t) (erase_ssubset ht) (fun w hw => pos w (mem_of_mem_erase hw))
      have cnt := card_erase_add_one ht
      have sm := sum_erase_add (s:=U) (fun a : ℕ => a) ht
      rw [←cnt] at card ⊢
      nlinarith
    · simp [not_nonempty_iff_eq_empty.mp ne]

private lemma square_tau {a : ℕ} (sq : Squarefree a) :
    σ 0 a=2^a.primeFactors.card := by
  rw [ArithmeticFunction.sigma_zero_apply,Nat.card_divisors sq.ne_zero]
  calc
    _ = ∏ _p∈a.primeFactors, 2 := by
      apply prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree sq (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)]
    _ = _ := by simp



private lemma pair (f : Fin 7 → ℕ) (pos : ∀ i, 0<f i) (small : (∑ i,f i)≤27) :
    ∃ i j, i<j ∧ f i=f j := by
  by_contra! diff
  have inj : Function.Injective f := by
    intro a b eq
    rcases lt_trichotomy a b with ab|ab|ab
    · exact False.elim (diff a b ab eq)
    · exact ab
    · exact False.elim (diff b a ab eq.symm)
  have lo := distinct_sum (univ.image f) (by
    intro t ht
    obtain ⟨a,_,rfl⟩ := mem_image.mp ht
    exact pos a)
  rw [card_image_of_injective _ inj,sum_image inj.injOn] at lo
  simp only [card_univ,Fintype.card_fin] at lo
  omega

private lemma adjacent {a b d n p q u v : ℕ} (ab : a<b) (ddef : d=b-a)
    (dg : d=a.gcd b)
    (key : σ 0 a * σ 0 (b/d) = σ 0 b * σ 0 (a/d))
    (pv : p*v=a*n+1) (qu : q*u=b*n+1)
    (pt : σ 0 p=σ 0 a) (qt : σ 0 q=σ 0 b) (uv : σ 0 u=σ 0 v)
    (bp : (b/d).Coprime p) (aq : (a/d).Coprime q)
    (vc : ((b/d)*p).Coprime v) (uc : ((a/d)*q).Coprime u) :
    σ 0 ((a/d)*(b*n+1)) = σ 0 ((a/d)*(b*n+1)+1) := by
  have ad : d∣a := dg ▸ Nat.gcd_dvd_left a b
  have bd : d∣b := dg ▸ Nat.gcd_dvd_right a b
  have dp : 0<d := by omega
  have da := Nat.div_mul_cancel ad
  have db := Nat.div_mul_cancel bd
  have quot : a/d+1=b/d := by
    apply Nat.eq_of_mul_eq_mul_right dp
    rw [Nat.add_mul,one_mul,da,db]
    omega
  have cross : a/d*b=b/d*a := by
    calc
      _ = a/d*((b/d)*d) := by rw [db]
      _ = b/d*((a/d)*d) := by ring
      _ = _ := by rw [da]
  have consec : (a/d)*(b*n+1)+1=(b/d)*(a*n+1) := by
    simp only [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    rw [cross]
    omega
  rw [consec,←qu,←pv,←Nat.mul_assoc,←Nat.mul_assoc]
  have mul := ArithmeticFunction.isMultiplicative_sigma (k:=0)
  rw [mul.map_mul_of_coprime uc,mul.map_mul_of_coprime vc,
    mul.map_mul_of_coprime aq,mul.map_mul_of_coprime bp,pt,qt,uv]
  nlinarith only [congrArg (fun x => x * σ 0 v) key]

end

set_option maxHeartbeats 1200000 in
theorem main : H1 → H2 → type_of% @Erdos946.erdos_946.variants.heathbrown_lower_bound := by
  classical
  intro sieve hk
  obtain ⟨a,mono,pos,key⟩ := hk
  let A := a (Fin.last 6)
  have top (i : Fin 7) : a i≤A := mono.monotone (Fin.le_last i)
  let q (i:Fin 7) := Nat.nth Nat.Prime (A+i.val+1)
  have qp (i) : (q i).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have qi : Function.Injective q := by
    intro i j eq
    have h := Nat.nth_injective Nat.infinite_setOfPred_prime eq
    apply Fin.ext
    omega
  have aq (i j) : a i<q j := by
    have h : A+j.val+1≤q j := Nat.le_nth (fun hf => (Nat.infinite_setOfPred_prime hf).elim)
    have ai := top i
    omega
  let e (i : Fin 7) := σ 0 (a i) - 1
  let b (i : Fin 7) := q i ^ e i
  have bp (i) : 0<b i := pow_pos (qp i).pos _
  have bt (i) : σ 0 (b i)=σ 0 (a i) := by
    have pp := ArithmeticFunction.sigma_pos 0 (a i) (pos i).ne'
    rw [show b i=q i^e i from rfl,ArithmeticFunction.sigma_zero_apply_prime_pow (qp i)]
    dsimp [e]
    omega
  have cop (i j) : (a i).Coprime (b j) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    exact (qp j).coprime_iff_not_dvd.mpr (fun dv => (aq i j).not_ge (Nat.le_of_dvd (pos i) dv))
  let B := A * ∑ i, b i
  have denom (i j) (d : ℕ) : (a i/d)*b j≤B := Nat.mul_le_mul
    ((Nat.div_le_self _ _).trans (top i)) (single_le_sum_of_canonicallyOrdered (mem_univ j))
  let K := A*(A+1)
  have kp : 0<K := Nat.mul_pos (pos _) (by omega)
  have K1 : (1:ℝ)≤K := by exact_mod_cast kp
  obtain ⟨C,Cp,many⟩ := sieve a q e mono pos qi qp aq B
  refine Asymptotics.isBigO_iff.mpr ⟨(K:ℝ)*(C*49),?_⟩
  have kt : Tendsto (fun x : ℝ => x/(K:ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  filter_upwards [kt.eventually many,kt.eventually (eventually_gt_atTop (1:ℝ))] with x many large
  obtain ⟨U,rate,rows⟩ := many
  let V := (range (⌊x⌋₊+1)).filter (fun z => σ 0 z=σ 0 (z+1))
  let z (i j : Fin 7) (n : ℕ) := (a i/(a j-a i))*(a j*n+1)
  have get (n) (hn:n∈U) : ∃ i j : Fin 7, i<j ∧ z i j n∈V := by
    obtain ⟨np,nx,parts,total⟩ := rows n hn
    let v (i : Fin 7) := (a i*n+1)/b i
    have vp (i) : b i*v i=a i*n+1 := Nat.mul_div_cancel' (parts i).1
    obtain ⟨i,j,ij,eq⟩ := pair (fun i => (v i).primeFactors.card) (fun i =>
      card_pos.mpr (Nat.nonempty_primeFactors.mpr (parts i).2.1)) total
    have veq : σ 0 (v j)=σ 0 (v i) := by
      calc
        _ = 2^(v j).primeFactors.card := square_tau (parts j).2.2.1
        _ = 2^(v i).primeFactors.card := congrArg (2^·) eq.symm
        _ = _ := (square_tau (parts i).2.2.1).symm
    let d := a j-a i
    have da : d∣a i := by simpa only [d,(key i j ij).1] using Nat.gcd_dvd_left (a i) (a j)
    have db : d∣a j := by simpa only [d,(key i j ij).1] using Nat.gcd_dvd_right (a i) (a j)
    have rr (h t : Fin 7) (dd : d∣a h) : ((a h/d)*b t).Coprime (v t) := by
      apply Nat.coprime_of_dvd
      intro p pp pc pv
      have hh := (parts t).2.2.2 p (Nat.mem_primeFactors.mpr ⟨pp,pv,by
        change v t≠0; have := (parts t).2.1; change 1<v t at this; omega⟩)
      have dp : 0<a h/d := Nat.div_pos (Nat.le_of_dvd (pos h) dd) (by
        dsimp [d]; have := mono ij; omega)
      exact hh.not_ge ((Nat.le_of_dvd (Nat.mul_pos dp (bp t)) pc).trans (denom h t d))
    have hit := adjacent (mono ij) (d:=d) rfl (key i j ij).1 (key i j ij).2
      (vp i) (vp j) (bt i) (bt j) veq ((cop j i).of_dvd_left (Nat.div_dvd_of_dvd db))
      ((cop i j).of_dvd_left (Nat.div_dvd_of_dvd da)) (rr j i db) (rr i j da)
    have limit : z i j n ≤ K*n := by
      calc
        _ ≤ A*(A*n+1) := Nat.mul_le_mul ((Nat.div_le_self _ _).trans (top i))
          (by have := Nat.mul_le_mul_right n (top j); omega)
        _ ≤ A*((A+1)*n) := Nat.mul_le_mul_left _ (by nlinarith)
        _ = _ := by dsimp [K]; ring
    have realLimit : (z i j n:ℝ)≤x := by
      calc
        _ ≤ (K:ℝ)*n := by exact_mod_cast limit
        _ ≤ x := by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp nx
    exact ⟨i,j,ij,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor realLimit)),hit⟩⟩
  choose I J IJ mem using (fun n : U => get n n.property)
  let map (n : U) : Fin 7 × Fin 7 × V := (I n,J n,⟨_,mem n⟩)
  have inj : Function.Injective map := by
    intro n m h
    have hi : I n=I m := congrArg Prod.fst h
    have hj : J n=J m := congrArg (fun u => u.2.1) h
    have hz : z (I n) (J n) n=z (I m) (J m) m := congrArg (fun u => u.2.2.val) h
    rw [hi,hj] at hz
    let d := a (J m)-a (I m)
    have dvd : d∣a (I m) := by
      simpa only [d,(key _ _ (IJ m)).1] using Nat.gcd_dvd_left (a (I m)) (a (J m))
    have dp : 0<d := Nat.sub_pos_of_lt (mono (IJ m))
    have coeff := Nat.div_pos (Nat.le_of_dvd (pos _) dvd) dp
    have hz' := Nat.eq_of_mul_eq_mul_left coeff hz
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left (pos _) (Nat.add_right_cancel hz'))
  have nn := Fintype.card_le_of_injective map inj
  have count : (U.card:ℝ) ≤ 49 * Erdos946.erdos946Count x := by
    change (U.card:ℝ)≤49*(V.card:ℝ)
    simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] at nn
    exact_mod_cast (show U.card≤49*V.card by omega)
  have xp : 0<x := by have := (lt_div_iff₀ (by positivity : (0:ℝ)<K)).mp large; linarith
  have x1 : 1<x := by have := (lt_div_iff₀ (by positivity : (0:ℝ)<K)).mp large; linarith
  have logpos := Real.log_pos large
  have logle : log (x/K)≤log x := Real.log_le_log (by positivity)
    (div_le_self xp.le K1)
  have rate' : x / (log x)^7 ≤ (K:ℝ)*(x/K/(log (x/K))^7) := by
    calc
      _ ≤ x/(log (x/K))^7 := div_le_div_of_nonneg_left xp.le (by positivity)
        (pow_le_pow_left₀ logpos.le logle _)
      _ = _ := by field_simp
  rw [Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg xp.le (pow_nonneg (Real.log_pos x1).le 7)),
    abs_of_nonneg (show 0≤Erdos946.erdos946Count x by unfold Erdos946.erdos946Count; positivity)]
  exact rate'.trans (by calc
    _ ≤ (K:ℝ)*(C*U.card) := by gcongr
    _ ≤ (K:ℝ)*(C*(49*Erdos946.erdos946Count x)) := by gcongr
    _ = _ := by ring)

end OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1
