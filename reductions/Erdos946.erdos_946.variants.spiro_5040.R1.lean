import FormalConjectures.ErdosProblems.«946»

/-! Spiro's eight linear forms and a square-divisor estimate. Their slopes
are primes and all pairwise differences divide 5040. A lower sieve supplies
rough values with a small sum of prime-factor counts. The second input is
the elementary cost of removing square multiples, separate from the sieve.
Reference: C. A. Spiro, 1981 thesis; E. Hasanalizade, The Goldston–Pintz–Yıldırım
sieve and some applications, 2013, §3. -/

namespace OMA.R_Erdos946_erdos_946_variants_spiro_5040_R1
open Finset Filter
open scoped ArithmeticFunction.sigma Classical

/-- The dimension-eight almost-prime sieve, in a dyadic interval. A power
threshold for the least prime factor allows this weaker power-sized output
in place of the usual lower bound of order X/(log X)^8. -/
def H1 : Prop :=
  let P : Finset ℕ := {11,17,23,29,41,47,53,59}
  ∃ k : ℕ, 2≤k ∧ ∀ᶠ B : ℕ in atTop,
    ∃ U : Finset ℕ, 2000*B^(k-1) ≤ U.card ∧ ∀ n∈U, B^k<n ∧ n≤2*B^k ∧
      (∀ q∈P, ∀ p∈(q*n+1).primeFactors, B<p) ∧
      (∑ q∈P, (q*n+1).primeFactors.card) ≤ 35

/-- Cost of removing multiples of squares of integers larger than B. -/
def H2 : Prop := ∀ B X : ℕ, 0<B → ∀ S : Finset ℕ,
    (∀ v∈S, 0<v ∧ v≤X ∧ ∃ d : ℕ, B<d ∧ d^2∣v) → B*S.card≤X

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

private lemma equal_counts (P : Finset ℕ) (pc : P.card=8) (f : ℕ→ℕ)
    (pos : ∀ p∈P, 0<f p) (small : (∑ p∈P,f p)≤35) :
    ∃ q∈P, ∃ t∈P, q<t ∧ f q=f t := by
  by_contra! diff
  have inj : Set.InjOn f (P:Set ℕ) := by
    intro a ha b hb eq
    rcases lt_trichotomy a b with ab|ab|ab
    · exact False.elim (diff a ha b hb ab eq)
    · exact ab
    · exact False.elim (diff b hb a ha ab eq.symm)
  have lo := distinct_sum (P.image f) (by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := mem_image.mp ht
    exact pos a ha)
  rw [card_image_of_injOn inj,pc,sum_image inj] at lo
  omega

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

private lemma shift {n q t : ℕ} (qt : q<t) (qp : q.Prime) (tp : t.Prime)
    (qcop : q.Coprime 5040) (tcop : t.Coprime 5040) (dvd : t-q∣5040)
    (left : (q*n+1).Coprime ((5040/(t-q))*t))
    (right : (t*n+1).Coprime ((5040/(t-q))*q))
    (equal : σ 0 (q*n+1) = σ 0 (t*n+1)) :
    ∃ z : ℕ, n≤z ∧ σ 0 z=σ 0 (z+5040) := by
  let h := 5040/(t-q)
  have hpos : 0<h := Nat.div_pos (Nat.le_of_dvd (by decide) dvd) (by omega)
  have hd : h*(t-q)=5040 := Nat.div_mul_cancel dvd
  have dh : h∣5040 := Nat.div_dvd_of_dvd dvd
  have ctr (a b : ℕ) (ab : a.Coprime b) :
      σ 0 (a*b)=σ 0 a*σ 0 b := ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ab
  have eq : (h*q)*(t*n+1)+5040=(h*t)*(q*n+1) := by
    have key : q+(t-q)=t := by omega
    calc
      _ = (h*q)*(t*n+1)+h*(t-q) := by rw [hd]
      _ = h*t*q*n+h*(q+(t-q)) := by ring
      _ = _ := by rw [key]; ring
  have st (p : ℕ) (hp:p.Prime) : σ 0 p=2 := by
    simpa using ArithmeticFunction.sigma_zero_apply_prime_pow (i:=1) hp
  refine ⟨(h*q)*(t*n+1),?_,?_⟩
  · have nt : n≤t*n := Nat.le_mul_of_pos_left _ tp.pos
    exact (show n≤t*n+1 by omega).trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos hpos qp.pos))
  · rw [eq,ctr _ _ right.symm,ctr _ _ left.symm,ctr _ _ (qcop.of_dvd_right dh).symm,
      ctr _ _ (tcop.of_dvd_right dh).symm,st q qp,st t tp,equal]

end

set_option maxHeartbeats 600000 in
theorem main : H1 → H2 → type_of% @Erdos946.erdos_946.variants.spiro_5040 := by
  classical
  intro sieve rare
  let P : Finset ℕ := {11,17,23,29,41,47,53,59}
  have pc : P.card=8 := by decide
  have spec : ∀ q∈P, q.Prime ∧ q.Coprime 5040 ∧ q≤59 := by
    intro q hq
    simp only [P,mem_insert,mem_singleton] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have diffs : ∀ q∈P, ∀ t∈P, q<t → t-q∣5040 := by
    intro q hq t ht
    simp only [P,mem_insert,mem_singleton] at hq ht
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  obtain ⟨k,large,ev⟩ := sieve
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨B,⟨U,raw,rows⟩,deep,bN⟩ := (ev.and ((eventually_ge_atTop 300000).and
    (eventually_gt_atTop N))).exists
  have bp : 0<B := by omega
  let X := B^k
  have xp : 0<X := pow_pos bp _
  have ux (n) (hn:n∈U) : X<n ∧ n≤2*X := ⟨(rows n hn).1,(rows n hn).2.1⟩
  have rough (n) (hn:n∈U) (q) (hq:q∈P) (p) (hp:p.Prime) (dv:p∣q*n+1) : B<p :=
    (rows n hn).2.2.1 q hq p (Nat.mem_primeFactors.mpr ⟨hp,dv,by omega⟩)
  let bad (q : ℕ) := U.filter (fun n => ¬Squarefree (q*n+1))
  have bad_bound (q) (hq:q∈P) : B*(bad q).card≤119*X := by
    let f (n : ℕ) := q*n+1
    have qp := (spec q hq).1.pos
    have inj : Function.Injective f := by
      intro a b eq
      dsimp [f] at eq
      exact Nat.eq_of_mul_eq_mul_left qp (Nat.add_right_cancel eq)
    have bound := rare B (119*X) bp ((bad q).image f) (by
      intro z hz
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hz
      obtain ⟨un,nsq⟩ := mem_filter.mp hn
      obtain ⟨d,dp,dv⟩ : ∃ d : ℕ, d.Prime ∧ d*d∣q*n+1 := by
        simpa only [Nat.squarefree_iff_prime_squarefree,not_forall,exists_prop,not_not] using nsq
      have dx : d∣q*n+1 := (dvd_mul_right d d).trans dv
      have ub := Nat.mul_le_mul (spec q hq).2.2 (ux n un).2
      exact ⟨by dsimp [f]; omega,by dsimp [f]; omega,d,rough n un q hq d dp dx,by simpa [pow_two] using dv⟩)
    simpa only [card_image_of_injective _ inj] using bound
  have rawbig : 2000*X≤B*U.card := by
    have pow : B^(k-1)*B=X := by rw [←pow_succ,show k-1+1=k by omega]
    calc
      _ = B*(2000*B^(k-1)) := by rw [←pow]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ raw
  have good : ∃ n∈U, ∀ q∈P, Squarefree (q*n+1) := by
    by_contra! no
    have sub : U⊆P.biUnion bad := by
      intro n hn
      obtain ⟨q,hq,ns⟩ := no n hn
      exact mem_biUnion.mpr ⟨q,hq,mem_filter.mpr ⟨hn,ns⟩⟩
    have cap : B*U.card ≤ 8*(119*X) := by
      calc
        _ ≤ B*∑ q∈P,(bad q).card := Nat.mul_le_mul_left _ ((card_le_card sub).trans card_biUnion_le)
        _ = ∑ q∈P,B*(bad q).card := mul_sum ..
        _ ≤ ∑ _q∈P,119*X := sum_le_sum fun q hq => bad_bound q hq
        _ = _ := by simp [pc]
    omega
  obtain ⟨n,hn,sq⟩ := good
  have np : 0<n := xp.trans (ux _ hn).1
  have pos (q) (hq:q∈P) : 0<(q*n+1).primeFactors.card :=
    card_pos.mpr (Nat.nonempty_primeFactors.mpr (by have := Nat.mul_pos (spec q hq).1.pos np; omega))
  obtain ⟨q,hq,t,ht,qt,counts⟩ := equal_counts P pc (fun q => (q*n+1).primeFactors.card)
    pos (rows n hn).2.2.2
  have eq : σ 0 (q*n+1)=σ 0 (t*n+1) := by rw [square_tau (sq _ hq),square_tau (sq _ ht),counts]
  let H := 5040/(t-q)
  have hp : 0<H := Nat.div_pos (Nat.le_of_dvd (by decide) (diffs q hq t ht qt)) (by omega)
  have small (a) (ha:a∈P) : H*a≤B := by
    have h := Nat.mul_le_mul (Nat.div_le_self 5040 (t-q)) (spec a ha).2.2
    change (5040/(t-q))*a≤B
    omega
  have cop (a) (ha:a∈P) (c) (cp:0<c) (cb:c≤B) : (a*n+1).Coprime c := by
    apply Nat.coprime_of_dvd
    intro p pp pa pc'
    exact (rough n hn a ha p pp pa).not_ge ((Nat.le_of_dvd cp pc').trans cb)
  obtain ⟨z,zn,ze⟩ := shift qt (spec q hq).1 (spec t ht).1 (spec q hq).2.1 (spec t ht).2.1
    (diffs q hq t ht qt) (cop q hq _ (Nat.mul_pos hp (spec t ht).1.pos) (small t ht))
    (cop t ht _ (Nat.mul_pos hp (spec q hq).1.pos) (small q hq)) eq
  have bx : B≤X := Nat.le_self_pow (by omega) _
  exact ⟨z,ze,bN.trans_le (bx.trans ((ux n hn).1.le.trans zn))⟩

end OMA.R_Erdos946_erdos_946_variants_spiro_5040_R1
