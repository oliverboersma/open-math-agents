import FormalConjectures.ErdosProblems.«852»
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Chebyshev

/-! A polynomial lower bound for distinct consecutive prime gaps. Repeated gaps
in a short interval produce either three primes in arithmetic progression or
four primes at the corners of an additive rectangle. A finite upper-bound
sieve makes such intervals rare compared with the number of blocks of primes.
See the discussion of Erdős problem 852 (https://www.erdosproblems.com/forum/thread/852). -/

noncomputable section
open Finset Filter Asymptotics
namespace PairWindows

private def bad (t : Finset ℕ) (p : ℕ) : Finset ℕ := t.image fun a => (p-a%p)%p
private def rho (t : Finset ℕ) (p : ℕ) := (bad t p).card
private def mult (t : Finset ℕ) (d : ℕ) := ∏ p ∈ d.primeFactors, rho t p
private def localVal (t : Finset ℕ) (p r : ℕ) : ℝ := (rho t p:ℝ)/p - (if r ∈ bad t p then 1 else 0)
private def K (t : Finset ℕ) (d n : ℕ) : ℝ := ∏ p ∈ d.primeFactors, localVal t p (n%p)

private theorem bad_subset (t : Finset ℕ) {p : ℕ} (hp : 0 < p) : bad t p ⊆ range p := by
  intro r hr
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hr
  exact Finset.mem_range.mpr (Nat.mod_lt _ hp)

private theorem val_bound (t : Finset ℕ) {p : ℕ} (hp : p.Prime) (r : ℕ) : |localVal t p r| ≤ 1 := by
  have h : (rho t p:ℝ)/(p:ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hp.pos)).2 (by
    exact_mod_cast (Finset.card_le_card (bad_subset t hp.pos)).trans_eq (Finset.card_range p))
  unfold localVal
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [show (0:ℝ) ≤ (rho t p:ℝ)/p by positivity]

private theorem K_bound (t : Finset ℕ) (d n : ℕ) : |K t d n| ≤ 1 := by
  rw [K,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p hp => val_bound t (Nat.prime_of_mem_primeFactors hp) _)

private theorem K_prime (t : Finset ℕ) {d n : ℕ} (hd : Squarefree d)
    (hpr : ∀ a ∈ t, (n+a).Prime) (hlt : d < n) : K t d n = (mult t d:ℝ)/(d:ℝ) := by
  have no (p : ℕ) (hp : p ∈ d.primeFactors) : n%p ∉ bad t p := by
    have pp := Nat.prime_of_mem_primeFactors hp
    have pl := (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) (Nat.dvd_of_mem_primeFactors hp)).trans_lt hlt
    intro h
    obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp h
    have dvd : p ∣ n+a := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod,←eq]
      by_cases ht : a%p=0
      · simp [ht]
      · have r := Nat.mod_lt a pp.pos
        rw [Nat.mod_eq_of_lt (show p-a%p < p by omega),Nat.sub_add_cancel r.le,Nat.mod_self]
    have pe := (Nat.prime_dvd_prime_iff_eq pp (hpr a ha)).mp dvd
    omega
  unfold K mult
  push_cast
  calc
    _ = ∏ p ∈ d.primeFactors, ((rho t p:ℝ)/p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [localVal,no p hp]
    _ = _ := by
      rw [Finset.prod_div_distrib]
      congr 1
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]

private theorem crt_sum (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (start : ℕ)
    (g : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range (∏ p ∈ P, p), ∏ p ∈ P, g p ((start+i)%p) =
    ∏ p ∈ P, ∑ j ∈ Finset.range p, g p j := by
  classical
  let a (p : P) := p.val
  have hne (p : P) : a p ≠ 0 := (hp _ p.prop).ne_zero
  let (p : P) : NeZero (a p) := ⟨hne p⟩
  let m := ∏ p : P, a p
  have : NeZero m := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => hne p)⟩
  let e := ZMod.prodEquivPi a (fun i j hij => (Nat.coprime_primes (hp _ i.prop) (hp _ j.prop)).mpr
    (fun eq => hij (Subtype.ext eq)))
  let shift := Equiv.addLeft (start : ZMod m)
  let F (v : (p : P) → ZMod (a p)) := ∏ p, g p.val (v p).val
  have aux (q : ℕ) [NeZero q] (i : Fin q) : ZMod.finEquiv q i = (i.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => apply Fin.ext; exact (Nat.mod_eq_of_lt i.isLt).symm
  have eqg (i : Fin m) : F (e (shift (ZMod.finEquiv m i))) = ∏ p ∈ P, g p ((start+i.val)%p) := by
    change (∏ p : P, g p.val ((e ((start:ZMod m)+ZMod.finEquiv m i)) p).val) = _
    rw [aux, ← Nat.cast_add]
    rw [map_natCast]
    change (∏ p : P, g p.val (((start+i.val:ℕ) : ZMod (a p)).val)) = _
    simp only [ZMod.val_natCast]
    exact Finset.prod_coe_sort P (fun p => g p ((start+i.val)%p))
  have hm : m = ∏ p ∈ P, p := Finset.prod_coe_sort P id
  rw [← hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin m, F (e (shift (ZMod.finEquiv m i))) := Finset.sum_congr rfl (fun i _ => (eqg i).symm)
    _ = ∑ v, F v := Equiv.sum_comp (((ZMod.finEquiv m).toEquiv.trans shift).trans e.toEquiv) F
    _ = ∏ p : P, ∑ j : ZMod (a p), g p.val j.val := (Fintype.prod_sum (fun (p : P) (j : ZMod (a p)) => g p.val j.val)).symm
    _ = ∏ p : P, ∑ j ∈ Finset.range p.val, g p.val j := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← Fin.sum_univ_eq_sum_range]
      symm
      calc
        _ = ∑ i : Fin (a p), g p.val (ZMod.finEquiv (a p) i).val := by
          apply Finset.sum_congr rfl
          intro i _
          rw [aux,ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt]
        _ = _ := Equiv.sum_comp (ZMod.finEquiv (a p)).toEquiv (fun j => g p.val j.val)
    _ = _ := Finset.prod_coe_sort P (fun p => ∑ j ∈ Finset.range p, g p j)

private def cell (t : Finset ℕ) (d p r : ℕ) : ℝ := if p ∈ d.primeFactors then localVal t p r else 1

private theorem K_extend (t : Finset ℕ) {d : ℕ} {P : Finset ℕ} (h : d.primeFactors ⊆ P) (n : ℕ) :
    K t d n = ∏ p ∈ P, cell t d p (n%p) := by
  calc
    _ = ∏ p ∈ d.primeFactors, cell t d p (n%p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [cell,hp]
    _ = _ := Finset.prod_subset h (by intro p _ hp; simp [cell,hp])

private theorem indicators (t : Finset ℕ) {p : ℕ} (hp : 0 < p) (x : ℝ) :
    (∑ r ∈ range p, if r ∈ bad t p then x else 0) = (rho t p:ℝ)*x := by
  rw [← Finset.sum_filter]
  have eq : (range p).filter (· ∈ bad t p) = bad t p := by
    ext r
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => bad_subset t hp h)
  simp [eq,rho]

private theorem local_zero (t : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, localVal t p r = 0 := by
  simp only [localVal,Finset.sum_sub_distrib,indicators t hp,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have h : (0:ℝ)<p := by exact_mod_cast hp
  field_simp
  ring

private theorem local_sq (t : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, localVal t p r * localVal t p r ≤ (rho t p:ℝ) := by
  let a := (rho t p:ℝ)/p
  have e (r : ℕ) : localVal t p r * localVal t p r =
      a^2 + (if r ∈ bad t p then 1-2*a else 0) := by
    unfold localVal; dsimp [a]; split_ifs <;> ring
  simp_rw [e]
  rw [Finset.sum_add_distrib,indicators t hp]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  dsimp [a]
  have h : (0:ℝ)<p := by exact_mod_cast hp
  field_simp
  nlinarith [sq_nonneg (rho t p:ℝ),mul_nonneg h.le (sq_nonneg (rho t p:ℝ))]

private def period (d e : ℕ) := ∏ p ∈ d.primeFactors ∪ e.primeFactors, p

private theorem period_property {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    0 < period d e ∧ period d e ≤ d*e := by
  let P := d.primeFactors ∪ e.primeFactors
  have pp (p) (hp : p ∈ P) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have h1 : 0 < period d e := Finset.prod_pos (fun p hp => (pp p hp).pos)
  have h2 : 0 < ∏ p ∈ d.primeFactors ∩ e.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).pos)
  refine ⟨h1, ?_⟩
  calc
    _ ≤ period d e * (∏ p ∈ d.primeFactors ∩ e.primeFactors, p) := Nat.le_mul_of_pos_right _ h2
    _ = d*e := by rw [period,Finset.prod_union_inter,Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_of_squarefree he]

private theorem block (t : Finset ℕ) {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) (start : ℕ) :
    ∑ i ∈ range (period d e), K t d (start+i)*K t e (start+i) ≤
      if d=e then (mult t d:ℝ) else 0 := by
  let P := d.primeFactors ∪ e.primeFactors
  have pp (p) (hp : p ∈ P) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  let g (p r : ℕ) := cell t d p r * cell t e p r
  have ec (n : ℕ) : K t d n*K t e n = ∏ p ∈ P, g p (n%p) := by
    rw [K_extend t (P := P) Finset.subset_union_left, K_extend t (d := e) (P := P) Finset.subset_union_right,
      ← Finset.prod_mul_distrib]
  simp_rw [ec]
  change ∑ i ∈ range (∏ p ∈ P, p), _ ≤ _
  rw [crt_sum P pp start g]
  by_cases eq : d=e
  · subst e
    rw [if_pos rfl]
    change _ ≤ ((∏ p ∈ d.primeFactors, rho t p : ℕ):ℝ)
    push_cast
    dsimp [P]
    rw [Finset.union_idempotent]
    apply Finset.prod_le_prod
    · intro p _
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    · intro p hp
      simpa only [g,cell,if_pos hp] using local_sq t (Nat.prime_of_mem_primeFactors hp).pos
  · rw [if_neg eq]
    apply le_of_eq
    apply Finset.prod_eq_zero_iff.mpr
    have neq : d.primeFactors ≠ e.primeFactors := by
      intro hp
      have := congrArg (fun x : Finset ℕ => ∏ p ∈ x, p) hp
      simp [Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_of_squarefree he] at this
      contradiction
    obtain ⟨p,hp⟩ := Finset.ext_iff.not.mp neq |> Classical.not_forall.mp
    by_cases hpd : p ∈ d.primeFactors
    · have hpe : p ∉ e.primeFactors := by tauto
      have hm : p ∈ P := Finset.mem_union_left _ hpd
      exact ⟨p,hm,by simpa only [g,cell,if_pos hpd,if_neg hpe,mul_one] using local_zero t (pp p hm).pos⟩
    · have hpe : p ∈ e.primeFactors := by tauto
      have hm : p ∈ P := Finset.mem_union_right _ hpe
      exact ⟨p,hm,by simpa only [g,cell,if_neg hpd,if_pos hpe,one_mul] using local_zero t (pp p hm).pos⟩
private theorem interval_corr (t : Finset ℕ) {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) (start h : ℕ) :
    ∑ i ∈ range h, K t d (start+i)*K t e (start+i) ≤
      (if d=e then (h:ℝ)*mult t d/d else 0) + d*e := by
  let m := period d e
  have hm := (period_property hd he).1
  have hm0 : 0 < m := hm
  have hblocks (b : ℕ) :
      ∑ i ∈ range (b*m), K t d (start+i)*K t e (start+i) ≤ (b:ℝ)*(if d=e then (mult t d:ℝ) else 0) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,Nat.cast_succ,add_mul,one_mul]
      apply add_le_add ih
      simpa [Nat.add_assoc] using block t hd he (start+b*m)
  have hrest (b r : ℕ) : ∑ i ∈ range r, K t d (start+(b+i))*K t e (start+(b+i)) ≤ r := by
    calc
      _ ≤ ∑ i ∈ range r, (1:ℝ) := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans (by rw [abs_mul]; exact
          (mul_le_mul (K_bound t d _) (K_bound t e _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
      _ = _ := by simp
  have hx : h/m*m+h%m = h := Nat.div_add_mod' h m
  conv_lhs => rw [← hx,Finset.sum_range_add]
  have H := add_le_add (hblocks (h/m)) (hrest (h/m*m) (h%m))
  apply H.trans
  have hr : ((h%m:ℕ):ℝ) ≤ (d:ℝ)*e := by
    exact_mod_cast (Nat.mod_lt h hm0).le.trans (period_property hd he).2
  apply add_le_add _ hr
  by_cases eq : d=e
  · subst e
    have hdm : m=d := by simp [m,period,Nat.prod_primeFactors_of_squarefree hd]
    simp only [if_true,hdm]
    rw [le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hd.ne_zero : (0:ℝ) < d)]
    have hd' : ((h/d:ℕ):ℝ)*d ≤ h := by exact_mod_cast Nat.div_mul_le_self h d
    nlinarith [mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg (mult t d) : (0:ℝ) ≤ _)]
  · simp [eq]

private def divisorsTo (Q : ℕ) : Finset ℕ := (Icc 1 Q).filter Squarefree
private def mass (t : Finset ℕ) (Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, (mult t d:ℝ)/(d:ℝ)
private def kernel (t : Finset ℕ) (Q n : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, K t d n

private theorem energy (t : Finset ℕ) (start h Q : ℕ) :
    ∑ i ∈ range h, kernel t Q (start+i)^2 ≤ h*mass t Q + (Q:ℝ)^4 := by
  let D := divisorsTo Q
  have hd (d : ℕ) (h : d ∈ D) : d ≤ Q ∧ Squarefree d := by
    obtain ⟨h,h'⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_Icc.mp h).2,h'⟩
  have hcard : D.card ≤ Q := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (show (Icc 1 Q).card = Q by simp)
  have hsum (i : ℕ) : kernel t Q (start+i)^2 =
      ∑ d ∈ D, ∑ e ∈ D, K t d (start+i)*K t e (start+i) := by
    simp [kernel,D,pow_two,Finset.mul_sum,mul_comm]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D, ((if d=e then (h:ℝ)*mult t d/d else 0)+(Q:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro d hD
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro e hE
      apply (interval_corr t (hd d hD).2 (hd e hE).2 start h).trans
      apply add_le_add le_rfl
      exact_mod_cast (Nat.mul_le_mul (hd d hD).1 (hd e hE).1).trans_eq (pow_two Q).symm
    _ = h * mass t Q + (D.card:ℝ)^2*Q^2 := by
      simp [Finset.sum_add_distrib, mass,← Finset.mul_sum,div_eq_mul_inv,D,mul_assoc,pow_two]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ (Q:ℝ)^2*Q^2 := by gcongr
        _ = _ := by ring


private def sfMass (Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, 1/(d:ℝ)
private def zetaTwo : ℝ := ∑' n : ℕ, 1/(n:ℝ)^2

private theorem size_mass (Q : ℕ) : Real.log (Q+1 : ℕ) ≤ zetaTwo*sfMass Q := by
  classical
  let I := Finset.Icc 1 Q
  let D := divisorsTo Q
  choose a b eqn sf using Nat.sq_mul_squarefree
  let pair (n : ℕ) := (b n,a n)
  have hinj : Function.Injective pair := by
    intro n m h
    have eb : b n = b m := congrArg Prod.fst h
    have ea : a n = a m := congrArg Prod.snd h
    rw [←eqn n,eb,ea,eqn m]
  have sub : I.image pair ⊆ I ×ˢ D := by
    rintro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hn1,hnQ⟩ := Finset.mem_Icc.mp hn
    have e := eqn n
    have ha : 0 < a n := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at e; omega
    have hb : 0 < b n := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at e; omega
    have ha' := Nat.le_mul_of_pos_left (a n) (pow_pos hb 2)
    have hb' := Nat.le_mul_of_pos_right (b n ^ 2) ha
    have hb2 : b n ≤ b n^2 := by nlinarith
    change (b n,a n) ∈ I ×ˢ D
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb,by dsimp; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha,by dsimp; omega⟩,sf n⟩⟩
  let wt (u : ℕ × ℕ) : ℝ := (1/(u.1:ℝ)^2)*(1/(u.2:ℝ))
  calc
    _ ≤ (harmonic Q : ℝ) := log_add_one_le_harmonic Q
    _ = ∑ n ∈ I, wt (pair n) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro n _
      have e := eqn n
      dsimp [wt,pair]
      conv_lhs => rw [←e]
      push_cast
      simp [one_div,mul_comm]
    _ = ∑ u ∈ I.image pair, wt u := (Finset.sum_image hinj.injOn).symm
    _ ≤ ∑ u ∈ I ×ˢ D, wt u := Finset.sum_le_sum_of_subset_of_nonneg sub
        (fun _ _ _ => by dsimp [wt]; positivity)
    _ = (∑ b ∈ I, 1/(b:ℝ)^2)*sfMass Q := by
      rw [Finset.sum_product]
      simp [wt,D,sfMass,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => by positivity)
      exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum I (fun _ _ => by positivity)



private def tuples (t : Finset ℕ) (start h : ℕ) : Finset ℕ :=
  (range h).filter fun i => ∀ a ∈ t, (start+i+a).Prime

private theorem tuple_energy (t : Finset ℕ) {Q start h : ℕ} (hq : 1≤Q)
    (hr : Q<start) (hh : Q^4 ≤ h) :
    ((tuples t start h).card:ℝ)*mass t Q ≤ 2*h := by
  classical
  let M := mass t Q
  let P := tuples t start h
  have h1 : 1 ≤ M := by
    have hm : 1 ∈ divisorsTo Q := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hq⟩,by simp⟩
    have eq : (mult t 1:ℝ)/(1:ℝ)=1 := by simp [mult]
    rw [←eq]
    simpa only [Nat.cast_one,M,mass] using Finset.single_le_sum (f:=fun d : ℕ => (mult t d:ℝ)/(d:ℝ)) (fun d _ => by positivity) hm
  have cap : (P.card:ℝ)*M^2 ≤ h*M+(Q:ℝ)^4 := by
    calc
      _ = ∑ i ∈ P, kernel t Q (start+i)^2 := by
        have same (i : ℕ) (hi : i ∈ P) : kernel t Q (start+i) = M := by
          obtain ⟨_,hn⟩ := Finset.mem_filter.mp hi
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨hb,hsf⟩ := Finset.mem_filter.mp hd
          exact K_prime t hsf hn ((Finset.mem_Icc.mp hb).2.trans_lt (by omega))
        rw [Finset.sum_congr rfl (fun i hi => congrArg (·^2) (same i hi))]
        simp
      _ ≤ ∑ i ∈ range h, kernel t Q (start+i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := energy t start h _
  apply (le_of_mul_le_mul_right _ (by linarith : 0 < M))
  have hh' : (Q:ℝ)^4 ≤ h := by exact_mod_cast hh
  nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg h : (0:ℝ) ≤ _)]


private def value (S : Finset ℕ) : ℕ := ∏ p ∈ S, p
private def weight (l : ℕ) (S : Finset ℕ) : ℝ := ∏ p ∈ S, ((l:ℝ)/p)
private def euler (l : ℕ) (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1+(l:ℝ)/p)

private theorem weight_nn (l : ℕ) (S : Finset ℕ) : 0≤weight l S :=
  Finset.prod_nonneg (fun _ _ => by positivity)

private theorem total (l : ℕ) (P : Finset ℕ) : ∑ S ∈ P.powerset, weight l S = euler l P :=
  (Finset.prod_one_add P).symm

private theorem first_moment (l : ℕ) (P : Finset ℕ) (hP : ∀ p∈P, p.Prime) :
    ∑ S ∈ P.powerset, weight l S*(∑ p ∈ S, Real.log p) ≤
    euler l P*(∑ p ∈ P, (l:ℝ)/p*Real.log p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [weight,euler]
  | @insert p P hp ih =>
    have pp := hP p (Finset.mem_insert_self ..)
    have h := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq))
    let z : ℝ := (l:ℝ)/p
    let v := Real.log p
    let A := ∑ S ∈ P.powerset, weight l S*(∑ q ∈ S, Real.log q)
    let E := euler l P
    let F := ∑ q ∈ P, (l:ℝ)/q*Real.log q
    change A≤E*F at h
    have zp : 0≤z := by dsimp [z]; positivity
    have ep : 0≤E := Finset.prod_nonneg (fun _ _ => by positivity)
    have vp : 0≤v := Real.log_nonneg (by exact_mod_cast pp.one_lt.le)
    have ee : euler l (insert p P)=(1+z)*E := Finset.prod_insert hp
    have row (S : Finset ℕ) (hS : S∈P.powerset) :
        weight l (insert p S)*(∑ q ∈ insert p S, Real.log q) =
        (z*v)*weight l S + z*(weight l S*(∑ q ∈ S, Real.log q)) := by
      have pn : p∉S := fun hm => hp ((Finset.mem_powerset.mp hS) hm)
      rw [weight,Finset.prod_insert pn,Finset.sum_insert pn]
      dsimp [weight,z,v]; ring
    rw [Finset.sum_powerset_insert hp,Finset.sum_congr rfl row,Finset.sum_add_distrib,
      ←Finset.mul_sum,←Finset.mul_sum,total,ee,Finset.sum_insert hp]
    change A+(z*v*E+z*A) ≤ (1+z)*E*(z*v+F)
    nlinarith only [h,mul_le_mul_of_nonneg_left h zp,mul_nonneg (mul_nonneg (sq_nonneg z) vp) ep]

private theorem logs_primes (R : ℕ) (hR : 1≤R) :
    ∑ p ∈ Nat.primesLE R, Real.log p/(p:ℝ) ≤ 2*Real.log R := by
  classical
  let P := Nat.primesLE R
  let I := Ioc 0 R
  have rpos : (0:ℝ)<R := by exact_mod_cast hR
  have hr (n : ℕ) (hn : n∈I) : ∑ p ∈ P, (if p∣n then Real.log p else 0) ≤ Real.log R := by
    obtain ⟨h0,hN⟩ := Finset.mem_Ioc.mp hn
    have eq : P.filter (· ∣ n)=n.primeFactors := by
      ext p
      simp only [P,Finset.mem_filter,Nat.mem_primesLE,Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨_,pp⟩,dvd⟩; exact ⟨pp,dvd,h0.ne'⟩
      · rintro ⟨pp,dvd,_⟩; exact ⟨⟨(Nat.le_of_dvd h0 dvd).trans hN,pp⟩,dvd⟩
    rw [←Finset.sum_filter,eq,←Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero),←Nat.cast_prod]
    apply Real.log_le_log
    · exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    · exact_mod_cast (Nat.le_of_dvd h0 (Nat.prod_primeFactors_dvd n)).trans hN
  have col (p : ℕ) (hp : p∈P) : (R:ℝ)*(Real.log p/p) ≤ 2*(∑ n ∈ I, if p∣n then Real.log p else 0) := by
    obtain ⟨pr,pp⟩ := Nat.mem_primesLE.mp hp
    have p0 : (0:ℝ)<p := by exact_mod_cast pp.pos
    have lp := Real.log_nonneg (show (1:ℝ)≤p by exact_mod_cast pp.one_lt.le)
    rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
    have m := Nat.mod_lt R pp.pos
    have d := Nat.mod_add_div R p
    have d1 := Nat.div_pos pr pp.pos
    have h : R ≤ 2*(R/p)*p := by nlinarith [Nat.mul_le_mul_left p d1]
    have h' : (R:ℝ) ≤ 2*((R/p:ℕ):ℝ)*p := by exact_mod_cast h
    rw [←mul_div_assoc,div_le_iff₀ p0]
    nlinarith only [mul_le_mul_of_nonneg_right h' lp]
  have t := Finset.sum_le_sum col
  rw [←Finset.mul_sum,←Finset.mul_sum,Finset.sum_comm] at t
  have b := Finset.sum_le_sum hr
  simp only [Finset.sum_const,nsmul_eq_mul,I,Nat.card_Ioc,Nat.sub_zero] at b
  apply (mul_le_mul_iff_right₀ rpos).mp
  change (R:ℝ)*_ ≤ (R:ℝ)*_
  linarith only [t,b]

private def trunc (P : Finset ℕ) (Q : ℕ) := P.powerset.filter fun S => value S ≤ Q

private theorem trunc_mass {l R : ℕ} (P : Finset ℕ) (hp : P⊆Nat.primesLE R) (hl : l≤4) (hr : 1<R) :
    euler l P ≤ 2*(∑ S ∈ trunc P (R^32), weight l S) := by
  classical
  let T := trunc P (R^32)
  let U := P.powerset \ T
  let E := euler l P
  let L := Real.log R
  have lp : 0<L := Real.log_pos (by exact_mod_cast hr)
  have ep : 0≤E := Finset.prod_nonneg (fun _ _ => by positivity)
  have sp (p : ℕ) (h : p∈P) := (Nat.mem_primesLE.mp (hp h)).2
  have z (S : Finset ℕ) (hS : S∈P.powerset) : 0≤∑ p ∈ S, Real.log p :=
    Finset.sum_nonneg fun p h => Real.log_nonneg (by exact_mod_cast (sp p (Finset.mem_powerset.mp hS h)).one_lt.le)
  have each (S : Finset ℕ) (hS : S∈U) : 32*L*weight l S ≤ weight l S*(∑ p ∈ S, Real.log p) := by
    obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hS
    have sz : R^32 < value S := lt_of_not_ge (fun he => hn (Finset.mem_filter.mpr ⟨hm,he⟩))
    have rr : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
    have log := Real.log_le_log (pow_pos rr 32) (show (R:ℝ)^32 ≤ value S by exact_mod_cast sz.le)
    rw [Real.log_pow] at log
    dsimp [value] at log
    rw [Nat.cast_prod,Real.log_prod (fun p h => by exact_mod_cast (sp p (Finset.mem_powerset.mp hm h)).ne_zero)] at log
    dsimp [L]; nlinarith only [mul_le_mul_of_nonneg_right log (weight_nn l S)]
  have ht := Finset.sum_le_sum each
  rw [←Finset.mul_sum] at ht
  have hsub : ∑ S ∈ U, weight l S*(∑ p ∈ S, Real.log p) ≤
      ∑ S ∈ P.powerset, weight l S*(∑ p ∈ S, Real.log p) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun S h _ => mul_nonneg (weight_nn l S) (z S h))
  have summ : ∑ p ∈ P, (l:ℝ)/p*Real.log p ≤ 8*L := by
    calc
      _ = (l:ℝ)*∑ p ∈ P, Real.log p/p := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      _ ≤ (l:ℝ)*∑ p ∈ Nat.primesLE R, Real.log p/p := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum_of_subset_of_nonneg hp (fun p h _ => div_nonneg
          (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp h).2.one_lt.le)) (Nat.cast_nonneg _))
      _ ≤ _ := by
        have hl' : (l:ℝ)≤4 := by exact_mod_cast hl
        exact le_trans (mul_le_mul_of_nonneg_left (logs_primes R hr.le) (Nat.cast_nonneg _))
          (by dsimp [L] at lp ⊢; nlinarith [mul_le_mul_of_nonneg_right hl' lp.le])
  have bound := ht.trans (hsub.trans ((first_moment l P sp).trans (mul_le_mul_of_nonneg_left summ ep)))
  have all := Finset.sum_sdiff (f:=weight l) (show T⊆P.powerset from Finset.filter_subset ..)
  rw [total] at all
  change _+_=E at all
  change E ≤ 2*(∑ S ∈ T, weight l S)
  apply (mul_le_mul_iff_right₀ lp).mp
  nlinarith only [bound,congrArg (fun z : ℝ => L*z) all,mul_nonneg lp.le ep]


private theorem prime_data {P : Finset ℕ} {R : ℕ} (hp : P⊆Nat.primesLE R)
    {S : Finset ℕ} (hS : S∈P.powerset) :
    0<value S ∧ Squarefree (value S) ∧ (value S).primeFactors=S := by
  have pp (p : ℕ) (h : p∈S) := (Nat.mem_primesLE.mp (hp (Finset.mem_powerset.mp hS h))).2
  refine ⟨Finset.prod_pos (fun p h => (pp p h).pos),?_,Nat.primeFactors_prod pp⟩
  clear hS hp
  induction S using Finset.induction_on with
  | empty => simp [value]
  | @insert p S hn ih =>
    have h := pp p (Finset.mem_insert_self ..)
    have qs (q : ℕ) (hq : q∈S) := pp q (Finset.mem_insert_of_mem hq)
    have qpos : 0<value S := Finset.prod_pos (fun q hq => (qs q hq).pos)
    have cop : p.Coprime (value S) := h.coprime_iff_not_dvd.mpr (fun hd => hn (by
      have mem := Nat.mem_primeFactors.mpr ⟨h,hd,qpos.ne'⟩
      rwa [show (value S).primeFactors=S from Nat.primeFactors_prod qs] at mem))
    rw [value,Finset.prod_insert hn]
    exact (Nat.squarefree_mul cop).mpr ⟨h.squarefree,ih qs⟩

private theorem weight_one (S : Finset ℕ) : weight 1 S=1/(value S:ℝ) := by
  simp [weight,value]

private theorem euler_small {R : ℕ} (hr : 1<R) :
    euler 1 (Nat.primesLE R) ≤ 2*(1+32*Real.log R) := by
  classical
  let P := Nat.primesLE R
  let Q := R^32
  let T := trunc P Q
  have data {S : Finset ℕ} (h : S∈T) : 0<value S ∧ Squarefree (value S) ∧ (value S).primeFactors=S := prime_data (P:=P) (R:=R) (fun _ e => e) (Finset.mem_filter.mp h).1
  have inj : Set.InjOn value ↑T := by
    intro S hs U hu e
    rw [←(data hs).2.2,←(data hu).2.2,e]
  have sub : T.image value ⊆ Icc 1 Q := by
    intro n hn
    obtain ⟨S,h,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨(data h).1,(Finset.mem_filter.mp h).2⟩
  have cap : ∑ S ∈ T, weight 1 S ≤ 1+32*Real.log R := by
    calc
      _ = ∑ n ∈ T.image value, 1/(n:ℝ) := by rw [Finset.sum_image inj]; simp_rw [weight_one]
      _ ≤ ∑ n ∈ Icc 1 Q, 1/(n:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
      _ ≤ 1+Real.log (Q:ℝ) := by
        simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using harmonic_le_one_add_log Q
      _ = _ := by simp [Q,Real.log_pow]
  exact (trunc_mass (l:=1) P (fun _ e => e) (by decide) hr).trans (by linarith)

private theorem euler_large (R : ℕ) : Real.log (R+1:ℕ) ≤ zetaTwo*euler 1 (Nat.primesLE R) := by
  classical
  let P := Nat.primesLE R
  let D := divisorsTo R
  have recon (d : ℕ) (h : d∈D) : value d.primeFactors=d :=
    Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp h).2
  have inj : Set.InjOn Nat.primeFactors ↑D := by
    intro d hd e he h
    rw [←recon d hd,←recon e he,h]
  have sub : D.image Nat.primeFactors ⊆ P.powerset := by
    intro S h
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp h
    apply Finset.mem_powerset.mpr
    intro p h
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors h).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2,Nat.prime_of_mem_primeFactors h⟩
  have cap : sfMass R ≤ euler 1 P := by
    rw [←total]
    calc
      _ = ∑ S ∈ D.image Nat.primeFactors, weight 1 S := by
        rw [Finset.sum_image inj]
        apply Finset.sum_congr rfl; intro d hd; rw [weight_one,recon d hd]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg sub (fun S _ _ => weight_nn 1 S)
  exact (size_mass R).trans (mul_le_mul_of_nonneg_left cap (tsum_nonneg fun _ => by positivity))

private theorem local_compare (l : ℕ) (hl : l≤4) {z : ℝ} (hz : 0≤z) (h1 : z≤1) :
    (1+z)^l ≤ (1+l*z)*Real.exp (16*z^2) := by
  have z2 : z^2≤z := by nlinarith [mul_nonneg hz (sub_nonneg.mpr h1)]
  have z3 : z^3≤z^2 := by nlinarith only [mul_le_mul_of_nonneg_right z2 hz]
  have z4 : z^4≤z^2 := by nlinarith only [pow_le_pow_left₀ (sq_nonneg z) z2 2]
  have a : (1+z)^l ≤ (1+l*z)*(1+16*z^2) := by
    interval_cases l <;> norm_num <;> nlinarith [sq_nonneg z,pow_nonneg hz 3]
  exact a.trans (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (16*z^2)]) (by positivity))

private theorem euler_compare (l : ℕ) (hl : l≤4) (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) :
    (euler 1 P)^l ≤ euler l P * Real.exp (16*zetaTwo) := by
  classical
  have ztot : ∑ p ∈ P, 1/(p:ℝ)^2 ≤ zetaTwo :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).sum_le_tsum P (fun _ _ => by positivity)
  calc
    _ = ∏ p ∈ P, (1+1/(p:ℝ))^l := by simp [euler,Finset.prod_pow]
    _ ≤ ∏ p ∈ P, ((1+(l:ℝ)/p)*Real.exp (16*(1/(p:ℝ))^2)) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p h
      simpa only [Nat.cast_one,mul_one_div] using local_compare l hl (by positivity : 0≤1/(p:ℝ))
        ((div_le_one (by exact_mod_cast (hp p h).pos)).mpr (by exact_mod_cast (hp p h).one_lt.le))
    _ = euler l P * Real.exp (16*∑ p ∈ P, 1/(p:ℝ)^2) := by
      rw [Finset.prod_mul_distrib,Finset.mul_sum,Real.exp_sum]; simp [euler]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (Finset.prod_nonneg fun _ _ => by positivity)

private theorem rho_of_large (t : Finset ℕ) {p W : ℕ} (hp : W<p) (tb : ∀ a∈t, a≤W) :
    rho t p = t.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  have a' := (tb a ha).trans_lt hp
  have b' := (tb b hb).trans_lt hp
  change (p-a%p)%p=(p-b%p)%p at he
  rw [Nat.mod_eq_of_lt a',Nat.mod_eq_of_lt b'] at he
  by_cases x : a=0 <;> by_cases y : b=0
  · omega
  · simp only [x,Nat.sub_zero,Nat.mod_self,Nat.mod_eq_of_lt (show p-b<p by omega)] at he
    omega
  · simp only [y,Nat.sub_zero,Nat.mod_self,Nat.mod_eq_of_lt (show p-a<p by omega)] at he
    omega
  · rw [Nat.mod_eq_of_lt (show p-a<p by omega),Nat.mod_eq_of_lt (show p-b<p by omega)] at he; omega

private theorem euler_mass (t : Finset ℕ) {W R : ℕ} (_wr : W≤R) (hr : 1<R)
    (hl : t.card≤4) (tb : ∀ a∈t, a≤W) :
    euler t.card (Nat.primesLE R \ Nat.primesLE W) ≤ 2*mass t (R^32) := by
  classical
  let P := Nat.primesLE R \ Nat.primesLE W
  let Q := R^32
  let A := trunc P Q
  have hp : P⊆Nat.primesLE R := Finset.sdiff_subset
  have data {S : Finset ℕ} (h : S∈A) : 0<value S ∧ Squarefree (value S) ∧ (value S).primeFactors=S := prime_data hp (Finset.mem_filter.mp h).1
  have inj : Set.InjOn value ↑A := by
    intro S hs U hu e; rw [←(data hs).2.2,←(data hu).2.2,e]
  have sub : A.image value ⊆ divisorsTo Q := by
    intro n hn; obtain ⟨S,h,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(data h).1,(Finset.mem_filter.mp h).2⟩,(data h).2.1⟩
  have w (S : Finset ℕ) (hs : S∈A) : weight t.card S=(mult t (value S):ℝ)/(value S:ℝ) := by
    have sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    dsimp [weight,mult]; rw [(data hs).2.2,Nat.cast_prod,Finset.prod_div_distrib]
    congr 1
    swap
    · simp [value]
    apply Finset.prod_congr rfl
    intro p h
    have x := Finset.mem_sdiff.mp (sub h)
    have ppr := (Nat.mem_primesLE.mp x.1).2
    rw [rho_of_large t (by by_contra! bad; exact x.2 (Nat.mem_primesLE.mpr ⟨bad,ppr⟩)) tb]
  have m : (∑ S ∈ A, weight t.card S) ≤ mass t Q := by
    calc
      _ = ∑ d ∈ A.image value, (mult t d:ℝ)/d := by rw [Finset.sum_image inj]; exact Finset.sum_congr rfl w
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
  exact (trunc_mass P hp hl hr).trans (by linarith)


private theorem primes_mono {a b : ℕ} (h : a≤b) : Nat.primesLE a ⊆ Nat.primesLE b := by
  intro p hp; obtain ⟨ha,pp⟩ := Nat.mem_primesLE.mp hp
  exact Nat.mem_primesLE.mpr ⟨ha.trans h,pp⟩

private theorem sieve_tuple (t : Finset ℕ) {W R M H : ℕ} (w1 : 1<W) (wr : W≤R)
    (ltM : R^32<M) (hh : (R^32)^4 ≤ H) (hl : t.card≤4) (ht : ∀ a∈t, a≤W) :
    ((tuples t M H).card:ℝ)*Real.log R^t.card ≤
      4*Real.exp (16*zetaTwo)*(H:ℝ)*(zetaTwo*(2*(1+32*Real.log W)))^t.card := by
  let P := Nat.primesLE R \ Nat.primesLE W
  let E := euler 1 P
  let A := zetaTwo*(2*(1+32*Real.log W))
  have r1 : 1<R := w1.trans_le wr
  have lp := Real.log_nonneg (show (1:ℝ)≤W by exact_mod_cast w1.le)
  have lr := Real.log_nonneg (show (1:ℝ)≤R by exact_mod_cast r1.le)
  have z : 0≤zetaTwo := tsum_nonneg (fun _ => by positivity)
  have ap : 0≤A := by dsimp [A]; positivity
  have ep : 0≤E := Finset.prod_nonneg (fun _ _ => by positivity)
  have ea := euler_small w1
  have ed : E*euler 1 (Nat.primesLE W)=euler 1 (Nat.primesLE R) := Finset.prod_sdiff (primes_mono wr)
  have logle : Real.log R≤A*E := by
    have le := Real.log_le_log (show (0:ℝ)<R by exact_mod_cast (show 0<R by omega))
      (show (R:ℝ) ≤ (R+1:ℕ) by exact_mod_cast Nat.le_add_right R 1)
    have big := euler_large R
    rw [←ed] at big
    dsimp [A]
    nlinarith only [le,big,mul_le_mul_of_nonneg_left ea (mul_nonneg z ep)]
  have ec := euler_compare t.card hl P (fun p hp => (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2)
  change E^t.card ≤ _ at ec
  have em := euler_mass t wr r1 hl ht
  have eu : E^t.card ≤ 2*mass t (R^32)*Real.exp (16*zetaTwo) :=
    ec.trans (mul_le_mul_of_nonneg_right em (Real.exp_pos _).le)
  have c := tuple_energy t (Q:=R^32) (Nat.one_le_pow _ _ r1.le) ltM hh
  have bound := pow_le_pow_left₀ lr logle t.card
  rw [mul_pow] at bound
  have b := bound.trans (mul_le_mul_of_nonneg_left eu (pow_nonneg ap _))
  have cb := mul_le_mul_of_nonneg_left b (Nat.cast_nonneg (tuples t M H).card (α:=ℝ))
  change _ ≤ _*(A^t.card)
  nlinarith only [cb,mul_le_mul_of_nonneg_right c (mul_nonneg (pow_nonneg ap t.card) (Real.exp_pos (16*zetaTwo)).le)]

private def R (j : ℕ) := 2^(j^32)
private def M (j : ℕ) := (R j)^256
private def W (j : ℕ) := 34359738368*j^33
private def H (j : ℕ) := 2147483648*j^32*M j

private theorem scale_params : ∀ᶠ j : ℕ in atTop,
    1<W j ∧ W j≤R j ∧ R j^32<M j ∧ (R j^32)^4≤H j := by
  filter_upwards [eventually_ge_atTop 40] with j hj
  have j1 : 1≤j := by omega
  have j2 : j≤2^j := Nat.lt_two_pow_self.le
  have j3 : 34*j ≤ j^32 := by
    have h : j^2≤j^32 := Nat.pow_le_pow_right j1 (by decide)
    nlinarith [Nat.mul_le_mul_left j (show 34≤j by omega)]
  have cap : 34359738368 ≤ (2:ℕ)^j := (by decide : 34359738368 ≤ 2^40).trans (Nat.pow_le_pow_right (by decide) hj)
  have pos : 1≤j^32 := Nat.one_le_pow _ _ j1
  have rp : 1<R j := one_lt_pow₀ (by decide) (by positivity : j^32≠0)
  have mp : 0<M j := by dsimp [M]; positivity
  refine ⟨by dsimp [W]; nlinarith [Nat.one_le_pow 33 j j1],?_,pow_lt_pow_right₀ rp (by decide : 32<256),?_⟩
  · calc
      W j ≤ (2^j)^34 := by
        change _*j^33 ≤ _
        rw [show (34:ℕ)=33+1 by decide,pow_succ (2^j) 33,mul_comm ((2^j)^33)]
        exact Nat.mul_le_mul cap (Nat.pow_le_pow_left j2 33)
      _ ≤ R j := by rw [←pow_mul]; dsimp [R]; apply Nat.pow_le_pow_right (by decide); omega
  · rw [←pow_mul]
    have a : R j^(32*4) ≤ M j := pow_le_pow_right₀ rp.le (by decide : 32*4≤256)
    exact a.trans (by dsimp [H]; nlinarith)

private theorem uniform_sieve : ∃ C : ℝ, 1≤C ∧ ∀ᶠ j : ℕ in atTop, ∀ t : Finset ℕ,
    (t.card=3 ∨ t.card=4) → (∀ a∈t, a≤W j) →
    ((tuples t (M j) (H j)).card:ℝ)*(j:ℝ)^(32*t.card) ≤ C*(H j)*(j:ℝ)^4 := by
  let K := (1+zetaTwo)*(2*(1+32*(Real.log 34359738368 + 33)))
  have z : 0≤zetaTwo := tsum_nonneg (fun _ => by positivity)
  have log0 : 0≤Real.log 34359738368 := Real.log_nonneg (by norm_num)
  have K1 : 1≤K := by dsimp [K]; nlinarith [mul_nonneg z log0]
  let C := 1+64*Real.exp (16*zetaTwo)*K^4
  have ep := Real.exp_pos (16*zetaTwo)
  refine ⟨C,le_add_of_nonneg_right (by positivity),?_⟩
  filter_upwards [scale_params,eventually_ge_atTop 1] with j hs hj t hcard ht
  obtain ⟨wp,wr,rm,rh⟩ := hs
  have h4 : t.card≤4 := by omega
  have jr : (1:ℝ)≤j := by exact_mod_cast hj
  have jp : (0:ℝ)<j := by linarith
  have hlog : Real.log (W j) = Real.log 34359738368+33*Real.log j := by
    simp [W,Real.log_mul (by norm_num : (34359738368:ℝ)≠0) (by positivity : (j:ℝ)^33≠0),Real.log_pow]
  have lu : Real.log (W j) ≤ (Real.log 34359738368+33)*j := by
    rw [hlog]
    nlinarith only [Real.log_le_sub_one_of_pos jp,mul_le_mul_of_nonneg_left jr log0]
  have lw := Real.log_nonneg (show (1:ℝ)≤W j by exact_mod_cast wp.le)
  have kl : zetaTwo*(2*(1+32*Real.log (W j))) ≤ K*j := by
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_left lu z,lu,jr,mul_nonneg z (sub_nonneg.mpr jr),mul_nonneg log0 jp.le]
  have low : (j:ℝ)^32/2 ≤ Real.log (R j) := by
    have hl : (1/2:ℝ) ≤ Real.log 2 := by
      convert Real.one_sub_inv_le_log_of_pos (x:=(2:ℝ)) (by norm_num) using 1
      norm_num
    simp [R,Real.log_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hl (pow_nonneg jp.le 32)]
  have cap := sieve_tuple t wp wr rm rh h4 ht
  let T : ℝ := (tuples t (M j) (H j)).card
  have tp : 0≤T := by dsimp [T]; positivity
  have m := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) low t.card) tp
  have u := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) kl t.card)
    (show 0≤4*Real.exp (16*zetaTwo)*(H j) by positivity)
  change T*_ ≤ _ at cap ⊢
  have ks : K^3≤K^4 := pow_le_pow_right₀ K1 (by decide)
  have js : (j:ℝ)^3≤(j:ℝ)^4 := pow_le_pow_right₀ jr (by decide)
  have plus : 0≤(H j:ℝ)*(j:ℝ)^4 := by positivity
  have eh : 0≤Real.exp (16*zetaTwo)*(H j:ℝ) := by positivity
  rcases hcard with h|h <;> rw [h] at m u cap ⊢ <;> dsimp [C] <;>
    nlinarith only [m,u,cap,plus,mul_le_mul_of_nonneg_left (mul_le_mul ks js (by positivity) (by positivity)) eh,
      mul_nonneg eh (mul_nonneg (by positivity : 0≤K^4) (by positivity : 0≤(j:ℝ)^4))]


private def Y (k : ℕ) : ℕ := (2^k)^16


private theorem logY (k : ℕ) : Real.log (Y k:ℝ)=16*k*Real.log 2 := by
  simp [Y,Real.log_pow]
  ring

private theorem Y_big : Tendsto Y atTop atTop := by
  have h : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  apply tendsto_atTop_mono (f:=fun k : ℕ => 2^k) _ h
  intro k
  exact Nat.le_self_pow (by decide) _

private theorem logtwo : (1/2:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · convert Real.one_sub_inv_le_log_of_pos (x:=(2:ℝ)) (by norm_num) using 1
    norm_num
  · convert Real.log_le_sub_one_of_pos (x:=(2:ℝ)) (by norm_num) using 1
    norm_num



private theorem many_primes : ∀ᶠ x : ℝ in atTop,
    x*Real.log 2/4 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ)*Real.log x := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2/4 by positivity),
    eventually_ge_atTop (8:ℝ)] with x hx h8
  have xp : 0 < x := by linarith
  have logx := Real.log_nonneg (by linarith : (1:ℝ) ≤ x)
  simp only [Real.norm_eq_abs,id_eq,abs_of_nonneg logx,abs_of_pos xp] at hx
  have hlog : Real.log (x+2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) xp.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have H := (div_le_iff₀ (Real.log_pos (by linarith : 1 < x))).mp
    (Chebyshev.pi_ge' (by linarith : 1 < x))
  nlinarith [mul_nonneg (sub_nonneg.mpr h8) hl.le]



private def X (k : ℕ) : ℕ := 134217728*k*Y k

private theorem y_pos (k : ℕ) : 0 < Y k := by unfold Y; positivity

private theorem y_step (k : ℕ) : Y (k+1) = 65536*Y k := by
  unfold Y; rw [pow_succ 2 k,mul_pow]; ring

private theorem prime_upper : ∀ᶠ k : ℕ in atTop, ∀ i ≤ 65536*Y k, Nat.nth Nat.Prime i ≤ X k := by
  have yk (k : ℕ) : k ≤ Y k := (Nat.lt_two_pow_self.le.trans (Nat.le_self_pow (by decide : 16≠0) _))
  have xge (k : ℕ) (hk : 1≤k) : Y k ≤ X k := by unfold X; nlinarith [y_pos k]
  have xt : Tendsto X atTop atTop := tendsto_atTop_mono' atTop
    ((eventually_ge_atTop 1).mono fun k hk => xge k hk) Y_big
  have tx : Tendsto (fun k : ℕ => (X k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp xt
  filter_upwards [tx.eventually many_primes,Y_big.eventually_ge_atTop 134217728,eventually_ge_atTop 1] with k hm hy hk i hi
  rw [Nat.floor_natCast] at hm
  have xcube : X k ≤ Y k ^ 3 := by
    unfold X; rw [pow_succ,pow_two]; gcongr; exact yk k
  have y : (0:ℝ)<Y k := by exact_mod_cast y_pos k
  have kr : (0:ℝ)<k := by exact_mod_cast hk
  have x : (0:ℝ)<X k := by exact_mod_cast (y_pos k).trans_le (xge k hk)
  have hlog := Real.log_le_log x (show (X k:ℝ) ≤ (Y k:ℝ)^3 by exact_mod_cast xcube)
  rw [Real.log_pow,logY] at hlog
  norm_num at hlog
  have hlu : Real.log (X k:ℝ) ≤ 48*k := by nlinarith [mul_le_mul_of_nonneg_left logtwo.2 kr.le]
  have hcount : 65536*Y k < (X k).primeCounting := by
    by_contra! hc
    have hcr : ((X k).primeCounting:ℝ) ≤ 65536*(Y k:ℝ) := by exact_mod_cast hc
    have hxp : (X k:ℝ)=134217728*(k:ℝ)*(Y k:ℝ) := by simp [X]
    have lo := mul_le_mul_of_nonneg_left logtwo.1 x.le
    have up := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (X k).primeCounting (α:=ℝ))
    have mid := mul_le_mul_of_nonneg_right hcr (show (0:ℝ)≤48*k by positivity)
    have chain := hm.trans (up.trans mid)
    rw [hxp] at lo chain
    nlinarith only [lo,chain,mul_pos kr y]
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count (hi.trans_lt hcount))



private abbrev primeAt := Nat.nth Nat.Prime

private theorem primeAt_strict : StrictMono primeAt := Nat.nth_strictMono (p:=Nat.Prime) Nat.infinite_setOfPred_prime

private theorem primeAt_prime (i : ℕ) : (primeAt i).Prime :=
  Nat.nth_mem_of_infinite (p:=Nat.Prime) Nat.infinite_setOfPred_prime i

private theorem scale_primes : ∀ᶠ j : ℕ in atTop, ∀ i≤2*M j, primeAt i ≤ H j := by
  have em (j : ℕ) : Y (16*j^32)=M j := by
    simp only [Y,M,R,←pow_mul]; congr 1; ring
  have eh (j : ℕ) : X (16*j^32)=H j := by rw [X,em,H]; ring
  have tend : Tendsto (fun j : ℕ => 16*j^32) atTop atTop := by
    apply tendsto_atTop_mono (f:=id) _ tendsto_id
    intro j
    exact (Nat.le_self_pow (by decide : 32≠0) j).trans (Nat.le_mul_of_pos_left _ (by decide))
  filter_upwards [tend.eventually prime_upper] with j h i hi
  rw [←eh]
  exact h i (by rw [em]; omega)

private def triples (m x w : ℕ) := (Icc 1 w).sigma (fun d => if d+d≤w then tuples {0,d,d+d} m x else ∅)
private def quads (m x w : ℕ) := (Icc 1 w ×ˢ Icc 1 w).sigma fun s : ℕ×ℕ =>
  if s.1<s.2 ∧ s.2+s.1≤w then tuples {0,s.1,s.2,s.2+s.1} m x else ∅

private lemma tuple_sizes : ∃ C : ℝ, 1≤C ∧ ∀ᶠ j : ℕ in atTop,
    ((triples (M j) (H j) (W j)).card:ℝ)*(j:ℝ)^96 ≤ C*(W j)*(H j)*(j:ℝ)^4 ∧
    ((quads (M j) (H j) (W j)).card:ℝ)*(j:ℝ)^128 ≤ C*(W j)^2*(H j)*(j:ℝ)^4 := by
  classical
  obtain ⟨C,cp,cap⟩ := uniform_sieve
  refine ⟨C,cp,?_⟩
  filter_upwards [cap] with j hc
  let w := W j
  let m := M j
  let x := H j
  let I := Icc 1 w
  have t (d : ℕ) (hd : d∈I) : (((if d+d≤w then tuples {0,d,d+d} m x else ∅).card):ℝ)*(j:ℝ)^96 ≤ C*x*(j:ℝ)^4 := by
    obtain ⟨d1,dw⟩ := Finset.mem_Icc.mp hd
    by_cases bound : d+d≤w
    · rw [if_pos bound]
      have sz : ({0,d,d+d} : Finset ℕ).card=3 := by
        rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert,Finset.mem_singleton]; omega),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega)]
        simp
      have h := hc {0,d,d+d} (Or.inl sz) (by intro a ha; simp only [Finset.mem_insert,Finset.mem_singleton] at ha; rcases ha with rfl|rfl|rfl <;> omega)
      simpa [sz,m,x] using h
    · rw [if_neg bound]; simp; positivity
  constructor
  · have sum := Finset.sum_le_sum t
    rw [←Finset.sum_mul,Finset.sum_const,nsmul_eq_mul] at sum
    simpa [triples,I,m,x,w,Finset.card_sigma,mul_assoc,mul_left_comm,mul_comm] using sum
  · let S (st : ℕ×ℕ) := if st.1<st.2 ∧ st.2+st.1≤w then tuples {0,st.1,st.2,st.2+st.1} m x else ∅
    have q (st : ℕ×ℕ) (he : st∈I ×ˢ I) : ((S st).card:ℝ)*(j:ℝ)^128 ≤ C*x*(j:ℝ)^4 := by
      obtain ⟨p,pw⟩ := Finset.mem_Icc.mp (Finset.mem_product.mp he).1
      obtain ⟨r,rw⟩ := Finset.mem_Icc.mp (Finset.mem_product.mp he).2
      dsimp [S]
      split_ifs with b
      · have sz : ({0,st.1,st.2,st.2+st.1} : Finset ℕ).card=4 := by
          rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert,Finset.mem_singleton]; omega),
            Finset.card_insert_of_notMem (by simp only [Finset.mem_insert,Finset.mem_singleton]; omega),
            Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega)]
          simp
        have h := hc _ (Or.inr sz) (by intro a ha; simp only [Finset.mem_insert,Finset.mem_singleton] at ha; rcases ha with rfl|rfl|rfl|rfl <;> omega)
        simpa [sz,m,x] using h
      · simp; positivity
    have sum := Finset.sum_le_sum q
    rw [←Finset.sum_mul,Finset.sum_const,nsmul_eq_mul] at sum
    simpa [quads,S,I,m,x,w,Finset.card_sigma,pow_two,mul_assoc,mul_left_comm,mul_comm] using sum


private abbrev Certificates := (Σ _ : ℕ, ℕ) ⊕ (Σ _ : ℕ×ℕ, ℕ)

private def offset : Certificates → ℕ
  | .inl x => x.2
  | .inr x => x.2

private theorem failure_pair {n j : ℕ} (h : ¬ Erdos852.DistinctGapRun n j) :
    ∃ i v : ℕ, n≤ i ∧ i< v ∧ v< n+j ∧ primeGap i=primeGap v := by
  classical
  by_contra! no
  apply h
  intro i hi v hv e
  obtain ⟨li,ui⟩ := Set.mem_Ico.mp hi
  obtain ⟨lv,uv⟩ := Set.mem_Ico.mp hv
  rcases lt_trichotomy i v with hp|rfl|hp
  · exact (no i v li hp uv e).elim
  · rfl
  · exact (no v i lv hp ui e.symm).elim

private theorem certificate {m x w n j : ℕ} (mp : 0< m) (mn : m≤ n)
    (high : primeAt (n+j)≤ x) (short : primeAt (n+j)-primeAt n ≤ w)
    (h : ¬ Erdos852.DistinctGapRun n j) :
    ∃ z ∈ (triples m x w).disjSum (quads m x w),
      ∃ i, n≤ i ∧ i< n+j ∧ m+offset z=primeAt i := by
  classical
  obtain ⟨i,v,ni,iv,vj,gap⟩ := failure_pair h
  let d := primeGap i
  let a := primeAt v-primeAt i
  let o := primeAt i-m
  have inc (k : ℕ) : primeAt (k+1)=primeAt k+primeGap k := by
    unfold primeGap; exact (Nat.add_sub_of_le (primeAt_strict (Nat.lt_succ_self k)).le).symm
  have di : 0< d := Nat.sub_pos_of_lt (primeAt_strict (Nat.lt_succ_self _))
  have ae : primeAt i+a=primeAt v := Nat.add_sub_of_le (primeAt_strict iv).le
  have aa : d≤ a := by have h := primeAt_strict.monotone (show i+1≤ v by omega); rw [inc] at h; dsimp [d]; omega
  have ni' := primeAt_strict.monotone ni
  have last := primeAt_strict.monotone (show v+1≤ n+j by omega)
  rw [inc v,←gap] at last
  have wd : a+d≤ w := by dsimp [d]; omega
  have pl : m≤ primeAt i := mn.trans (ni.trans ((Nat.le_add_right i 2).trans (Nat.add_two_le_nth_prime i)))
  have oe : m+o=primeAt i := Nat.add_sub_of_le pl
  have xo : o< x := by dsimp [o]; dsimp [d] at di; omega
  have mem (T : Finset ℕ) (hs : ∀ b∈T, (primeAt i+b).Prime) : o∈tuples T m x := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr xo,fun a ha => oe ▸ hs a ha⟩
  have pd : (primeAt i+d).Prime := inc i ▸ primeAt_prime (i+1)
  have pa : (primeAt i+a).Prime := ae ▸ primeAt_prime v
  have pda : (primeAt i+(a+d)).Prime := by
    rw [←Nat.add_assoc,ae]; change (primeAt v+primeGap i).Prime; rw [gap,←inc]; exact primeAt_prime _
  by_cases eq : d=a
  · let z : Certificates := .inl ⟨d,o⟩
    refine ⟨z,Finset.mem_disjSum.mpr ?_,i,ni,by omega,oe⟩
    have dw : d+d≤ w := by omega
    left
    refine ⟨⟨d,o⟩,?_,rfl⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨di,show d≤w by omega⟩,?_⟩
    dsimp only; rw [if_pos dw]; apply mem
    intro b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl
    · rw [Nat.add_zero]; exact primeAt_prime i
    · exact pd
    · simpa only [←eq] using pda
  · let z : Certificates := .inr ⟨(d,a),o⟩
    refine ⟨z,Finset.mem_disjSum.mpr ?_,i,ni,by omega,oe⟩
    right
    refine ⟨⟨(d,a),o⟩,?_,rfl⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨di,show d≤w by omega⟩,Finset.mem_Icc.mpr ⟨show 1≤a by omega,show a≤w by omega⟩⟩,?_⟩
    dsimp only; rw [if_pos (show d< a ∧ a+d≤ w from ⟨by omega,wd⟩)]
    apply mem
    intro b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl|rfl|rfl|rfl
    · rw [Nat.add_zero]; exact primeAt_prime i
    · exact pd
    · exact pa
    · exact pda

private theorem block_count {m x w j : ℕ} (mp : 0< m) (jp : 0< j)
    (hp : primeAt (2*m)≤ x) (bad : ∀ n< 2*m, ¬ Erdos852.DistinctGapRun n j) :
    (m/j)*w ≤ x+((triples m x w).card+(quads m x w).card)*w := by
  classical
  let B := m/j
  let start (b : ℕ) := m+b*j
  let span (b : ℕ) := primeAt (start (b+1))-primeAt (start b)
  let F := (range B).filter (fun b => span b≤ w)
  let G := range B \ F
  have be : B*j≤ m := Nat.div_mul_le_self m j
  have add (b : ℕ) : start (b+1)=start b+j := by dsimp [start]; ring
  have cap (b : ℕ) (hb : b< B) : start b< 2*m ∧ start b+j≤ 2*m := by
    have := Nat.mul_le_mul_right j (show b+1≤ B by omega)
    dsimp [start]; rw [Nat.add_mul] at this; omega
  have hsub : F⊆range B := Finset.filter_subset ..
  have cert (b : ℕ) (hb : b∈F) : ∃ z∈(triples m x w).disjSum (quads m x w),
      ∃ i, start b≤ i ∧ i< start b+j ∧ m+offset z=primeAt i := by
    obtain ⟨hr,hsp⟩ := Finset.mem_filter.mp hb
    have cb := cap b (Finset.mem_range.mp hr)
    exact certificate mp (Nat.le_add_right ..) ((primeAt_strict.monotone cb.2).trans hp)
      (by change primeAt (start (b+1))-_ ≤ _ at hsp; rw [add] at hsp; exact hsp) (bad _ cb.1)
  choose tag ht ix hlo hhi he using cert
  let f (b : ℕ) : Certificates := if h : b∈F then tag b h else .inl ⟨0,0⟩
  have inj : Set.InjOn f ↑F := by
    intro b hb c hc e
    change b∈F at hb
    change c∈F at hc
    dsimp [f] at e
    rw [dif_pos hb,dif_pos hc] at e
    have pi := (he b hb).symm.trans ((congrArg (fun z => m+offset z) e).trans (he c hc))
    have eq := primeAt_strict.injective pi
    have lb := hlo b hb; have ub := hhi b hb
    have lc := hlo c hc; have uc := hhi c hc
    by_contra ne
    rcases lt_or_gt_of_ne ne with bc|cb
    · have q := Nat.mul_le_mul_right j (show b+1≤ c by omega)
      rw [Nat.add_mul] at q; dsimp [start] at *; omega
    · have q := Nat.mul_le_mul_right j (show c+1≤ b by omega)
      rw [Nat.add_mul] at q; dsimp [start] at *; omega
  have nf : F.card ≤ (triples m x w).card+(quads m x w).card := by
    rw [←Finset.card_disjSum,←Finset.card_image_of_injOn inj]
    apply Finset.card_le_card
    intro z hz; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hz
    simpa only [f,dif_pos hb] using ht b hb
  have total (n : ℕ) : (∑ b ∈ range n, span b)+primeAt m=primeAt (start n) := by
    induction n with
    | zero => simp [start]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have p := primeAt_strict.monotone (show start n≤ start (n+1) by rw [add]; omega)
      dsimp only [span] at ih ⊢; omega
  have g (b : ℕ) (hb : b∈G) : w≤ span b := by
    obtain ⟨hb,hn⟩ := Finset.mem_sdiff.mp hb
    exact le_of_lt (lt_of_not_ge (fun e => hn (Finset.mem_filter.mpr ⟨hb,e⟩)))
  have ng : G.card*w ≤ x := by
    have h := Finset.sum_le_sum g
    simp only [Finset.sum_const,smul_eq_mul] at h
    have sub : ∑ b ∈ G, span b ≤ ∑ b ∈ range B, span b := Finset.sum_le_sum_of_subset_of_nonneg
      Finset.sdiff_subset (fun _ _ _ => Nat.zero_le _)
    have tl := total B
    have p := (primeAt_strict.monotone (show start B≤ 2*m by dsimp [start]; omega)).trans hp
    omega
  have cnt := Finset.card_sdiff_add_card_eq_card hsub
  change G.card+F.card=(range B).card at cnt
  rw [Finset.card_range] at cnt
  change B*w≤_
  rw [←cnt,Nat.add_mul]
  exact Nat.add_le_add ng (Nat.mul_le_mul_right w nf)


private theorem save_power {v m j c : ℝ} {l d : ℕ} (hm : 0≤ m) (hj : 1≤ j)
    (short : l+1≤ d) (cheap : 8*c≤ j) (cap : v*j^(d+1) ≤ c*m*j^l) :
    8*v*j≤ m := by
  have jp : 0< j := by linarith
  have scale : 8*c*m*j^l ≤ m*j^d := by
    calc
      _ ≤ j*m*j^l := by gcongr
      _ = m*j^(l+1) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj short) hm
  apply (mul_le_mul_iff_left₀ (pow_pos jp d)).mp
  rw [pow_succ] at cap
  nlinarith only [scale,cap]

private theorem good_block : ∀ᶠ j : ℕ in atTop, ∃ n< 2*M j, Erdos852.DistinctGapRun n j := by
  obtain ⟨C,cp,hC⟩ := tuple_sizes
  have tend : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hC,scale_primes,tend.eventually_ge_atTop (8*C*34359738368^2*2147483648),eventually_ge_atTop 2] with j hc hp large hj
  let m := M j
  let w := W j
  let x := H j
  let t := (triples m x w).card
  let q := (quads m x w).card
  have mp : 0< m := by dsimp [m,M,R]; positivity
  have wp : 0< w := by dsimp [w,W]; positivity
  have jp : 0< j := by omega
  have jr : (1:ℝ)≤ j := by exact_mod_cast (show 1≤ j by omega)
  have mr : (0:ℝ)< m := by exact_mod_cast mp
  have ww : (w:ℝ) =34359738368*(j:ℝ)^33 := by simp [w,W]
  have xx : (x:ℝ) =2147483648*(j:ℝ)^32*m := by simp [x,H,m]
  change (t:ℝ)*(j:ℝ)^96 ≤ C*(w:ℝ)*x*(j:ℝ)^4 ∧ (q:ℝ)*(j:ℝ)^128 ≤ C*(w:ℝ)^2*x*(j:ℝ)^4 at hc
  rw [ww,xx] at hc
  have tbound : 8*(t:ℝ)*j≤ m := by
    apply save_power (l:=69) (d:=95) (c:=C*34359738368*2147483648) mr.le jr (by decide) (by nlinarith only [large,cp])
    exact hc.1.trans_eq (by ring)
  have qbound : 8*(q:ℝ)*j≤ m := by
    apply save_power (l:=102) (d:=127) (c:=C*34359738368^2*2147483648) mr.le jr (by decide) (by linarith only [large])
    exact hc.2.trans_eq (by ring)
  have mj : j≤ m := by
    have j2 : j≤ 2^j := Nat.lt_two_pow_self.le
    have j32 : j≤ j^32 := Nat.le_self_pow (by decide) _
    exact ((j2.trans (Nat.pow_le_pow_right (by decide) j32))).trans (Nat.le_self_pow (by decide : 256≠0) _)
  let b := m/j
  have divp : 0< b := Nat.div_pos mj jp
  have dl : m≤ 2*b*j := by
    have r := Nat.mod_lt m jp
    have e := Nat.mod_add_div m j
    change m%j+j*b=m at e
    nlinarith [Nat.mul_le_mul_left j divp]
  have dl' : (m:ℝ) ≤ 2*(b:ℝ)*j := by exact_mod_cast dl
  by_contra! bad
  have hcount := block_count (w:=w) mp jp (hp (2*m) le_rfl) bad
  have rcount : (b:ℝ)*w ≤ x+((t:ℝ)+q)*w := by exact_mod_cast hcount
  have ident : 16*(j:ℝ)*x=m*w := by rw [ww,xx]; ring
  have wr : (0:ℝ)< w := by exact_mod_cast wp
  nlinarith only [mul_le_mul_of_nonneg_right dl' wr.le,
    mul_le_mul_of_nonneg_left rcount (show (0:ℝ)≤ 2*j by positivity),
    mul_le_mul_of_nonneg_right tbound wr.le,mul_le_mul_of_nonneg_right qbound wr.le,ident,mul_pos mr wr]

private theorem all_scales : ∃ c : ℝ, 0< c ∧ ∀ᶠ x : ℝ in atTop,
    ∃ n : ℕ, (n:ℝ)< x ∧ ∃ H : ℕ, (Real.log x)^c < (H:ℝ) ∧ Erdos852.DistinctGapRun n H := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp good_block
  let B (j : ℕ) : ℝ := 2*(M j:ℝ)
  have monoM : Monotone M := by
    intro a b h
    exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide : 0< 2) (Nat.pow_le_pow_left h 32)) 256
  have mono : Monotone B := by intro a b h; dsimp [B]; gcongr; exact_mod_cast monoM h
  have unbd (x : ℝ) : ∃ j, x< B j := by
    obtain ⟨n,hn⟩ := exists_nat_gt x
    refine ⟨n,hn.trans_le ?_⟩
    have h : n≤ M n := (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide : 0< 2)
      (Nat.le_self_pow (by decide : 32≠0) n))).trans (Nat.le_self_pow (by decide : 256≠0) _)
    dsimp [B]; exact_mod_cast h.trans (Nat.le_mul_of_pos_left _ (by decide : 0< 2))
  let J := N+2^42
  refine ⟨1/64,by norm_num,?_⟩
  filter_upwards [eventually_ge_atTop (B J)] with x hx
  let k := Nat.find (unbd x)
  have hi : x< B k := Nat.find_spec (unbd x)
  have jk : J< k := by
    by_contra! h; exact (hi.trans_le ((mono h).trans hx)).false
  let j := k-1
  have jj : j+1=k := by dsimp [j]; omega
  have jJ : J≤ j := by dsimp [j]; omega
  have lo : B j≤ x := le_of_not_gt (Nat.find_min (unbd x) (show j< k by omega))
  obtain ⟨n,hn,h⟩ := hN j (by dsimp [J] at jJ; omega)
  have jbig : (2:ℝ)^42 ≤ j := by exact_mod_cast (show 2^42≤ j by dsimp [J] at jJ; omega)
  have j1 : (1:ℝ)≤ j := by exact_mod_cast (show 1≤j by dsimp [J] at jJ; omega)
  have bm : 1≤ M j := by change 0<M j; dsimp [M,R]; positivity
  have x1 : 1≤ x := by
    have e : (1:ℝ)≤ M j := by exact_mod_cast bm
    dsimp [B] at lo
    linarith
  have el (a : ℕ) : Real.log (B a) = Real.log 2+256*((a:ℝ)^32)*Real.log 2 := by
    dsimp [B,M,R]; push_cast
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
    push_cast; ring
  have lu := Real.log_le_log (by linarith : 0< x) hi.le
  rw [←jj,el] at lu; push_cast at lu
  have log2 : Real.log 2≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)< 2)).trans_eq (by norm_num)
  have jp : 0< (j:ℝ) := by linarith
  have powle := pow_le_pow_left₀ (by positivity : (0:ℝ)≤ j+1) (by linarith : (j:ℝ)+1≤ 2*j) 32
  have jp32 : (j:ℝ)≤ (j:ℝ)^32 := by simpa using pow_le_pow_right₀ j1 (by decide : 1≤ 32)
  have big32 : (2:ℝ)^42 ≤ (j:ℝ)^32 := jbig.trans jp32
  have small : Real.log x < (j:ℝ)^64 := by
    nlinarith only [lu,log2,mul_le_mul_of_nonneg_left log2 (show 0≤ ((j:ℝ)+1)^32 by positivity),
      powle,mul_le_mul_of_nonneg_left big32 (pow_nonneg jp.le 32),jp32,j1]
  refine ⟨n,(show (n:ℝ)< B j by dsimp [B]; exact_mod_cast hn).trans_le lo,j,?_,h⟩
  calc
    _ < ((j:ℝ)^64)^(1/64:ℝ) := Real.rpow_lt_rpow (Real.log_nonneg x1) small (by norm_num)
    _ = (j:ℝ) := by rw [←Real.rpow_natCast_mul jp.le]; norm_num


end PairWindows

theorem OMA.solution : type_of% @Erdos852.erdos_852.parts.i := PairWindows.all_scales